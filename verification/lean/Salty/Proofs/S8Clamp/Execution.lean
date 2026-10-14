import Salty.Proofs.Core.CByteSyntax
import Salty.Proofs.Core.CByteMemory
import Salty.Generated.S8ClampNeon
import Salty.Generated.S8ClampRvv
import Salty.Proofs.S8Clamp.Stream

/-! Source-linked execution lemmas under development. No complete kernel
correctness theorem is claimed by this module. -/
set_option maxHeartbeats 1000000
namespace Salty.Kernels.S8Clamp.Execution
open CByte

/-- These are projections of the extracted program, not handwritten replacement
bodies. Changes to the generated control flow invalidate the proof reductions. -/
def rvvLoop : Stmt := firstStatement (dropStatements 6 Generated.S8Clamp.rvv)
def rvvBody : Stmt := loopBody rvvLoop
def neon64Body : Stmt := loopBody (firstStatement (dropStatements 6 Generated.S8Clamp.neon))
def neon8Body : Stmt := loopBody (firstStatement (dropStatements 7 Generated.S8Clamp.neon))

structure RvvLocals (s : State) (n : Nat) (input output : Address) (p : Params) : Prop where
  batch : s.locals "batch" = some (.integer n)
  inputPtr : s.locals "input" = some (.pointer input)
  outputPtr : s.locals "output" = some (.pointer output)
  min : s.locals "min" = some (.integer p.lo.toInt)
  max : s.locals "max" = some (.integer p.hi.toInt)

def rvvAfter (s : State) (n vl : Nat) (input output : Address) (bytes : List Byte)
    (m : Memory) : State :=
  let t := update s "vl" (.integer vl)
  let t := update t "vacc" (.vector 1 bytes)
  let t := { t with memory := m }
  let t := update t "input" (.pointer (input + BitVec.ofNat 64 vl))
  let t := update t "output" (.pointer (output + BitVec.ofNat 64 vl))
  update t "batch" (.integer (n - vl : Nat))

/-- Exact execution of one extracted RVV loop body, retaining its loads/stores,
pointer updates, scalar conversions and batch subtraction. Memory safety is
supplied as successful primitive accesses here and discharged by region lemmas
in a complete kernel contract. -/
theorem rvv_body_exec (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : Params) (bs : List Byte) (m : Memory)
    (locals : RvvLocals s n input output p) (bound : n < 2^64)
    (hlen : bs.length = cfg.choose n)
    (hload : loadBytes s.memory input (cfg.choose n) = some bs)
    (hstore : storeBytes s.memory output (bs.map (mainLane p)) = some m) :
    Exec cfg rvvBody s (rvvAfter s n (cfg.choose n) input output (bs.map (mainLane p)) m) := by
  have hvn : cfg.choose n ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
  have hvc : cfg.choose n ≤ cfg.capacity := Nat.le_trans (cfg.bounded n) (Nat.min_le_right ..)
  have ht (f : Byte → Byte) : (bs.map f).take (cfg.choose n) = bs.map f := by
    apply List.take_of_length_le
    simp [hlen]
  have ht0 : bs.take (cfg.choose n) = bs := by simp [← hlen]
  have hs : storeBytes s.memory output
      (bs.map (fun x => ByteISA.minSigned (ByteISA.maxSigned x p.lo) p.hi)) = some m := hstore
  apply run_sound (fuel := 20)
  simp +contextual [rvvBody, rvvLoop, loopBody, firstStatement, dropStatements, Generated.S8Clamp.rvv,
    run, eval, intrinsic, scalarLanes, effect, update, RvvLocals.batch locals,
    RvvLocals.inputPtr locals, RvvLocals.outputPtr locals, RvvLocals.min locals,
    RvvLocals.max locals, hlen, hload, hstore, hvc, hvn, cast_sub n _ hvn bound,
    rvvAfter, binary, ht, ht0, hs, mainLane, List.map_map, Function.comp_def]
  rfl

/-- Separation at the byte-access level. C object bounds and the parameter
region belong to the full caller contract, not to this local loop invariant. -/
structure RegionSafe (m : Memory) (input output : Address) (n : Nat) : Prop where
  readable : ∀ a, Footprint input n a → m.readable a = true
  writable : ∀ a, Footprint output n a → m.writable a = true
  separate : ∀ a, Footprint input n a → ¬ Footprint output n a

theorem RegionSafe.advance {m : Memory} {input output : Address} {n k : Nat}
    (safe : RegionSafe m input output n) (hk : k ≤ n) (bs : List Byte) (hlen : bs.length = k) :
    RegionSafe (writeBytes m output bs) (input + BitVec.ofNat 64 k)
      (output + BitVec.ofNat 64 k) (n - k) := by
  have sum : k + (n - k) = n := by omega
  constructor
  · intro a ha
    rw [writeBytes_readable]
    apply safe.readable a
    simpa only [sum] using footprint_shift input a (n - k) k ha
  · intro a ha
    rw [writeBytes_writable]
    apply safe.writable a
    simpa only [sum] using footprint_shift output a (n - k) k ha
  · intro a hi ho
    apply safe.separate a
    · simpa only [sum] using footprint_shift input a (n - k) k hi
    · simpa only [sum] using footprint_shift output a (n - k) k ho

theorem RegionSafe.remaining_read {m : Memory} {input output : Address} {n k : Nat}
    (safe : RegionSafe m input output n) (hk : k ≤ n) (bs : List Byte) (hlen : bs.length = k) :
    readBytes (writeBytes m output bs) (input + BitVec.ofNat 64 k) (n - k) =
      readBytes m (input + BitVec.ofNat 64 k) (n - k) := by
  apply readBytes_writeBytes_disjoint
  intro a hi ho
  apply safe.separate a
  · have h := footprint_shift input a (n - k) k hi
    simpa only [Nat.add_sub_cancel' hk] using h
  · exact footprint_mono (by omega) ho

theorem rvvAfter_locals (s : State) (n vl : Nat) (input output : Address) (p : Params)
    (bs : List Byte) (m : Memory) (h : RvvLocals s n input output p) :
    RvvLocals (rvvAfter s n vl input output bs m) (n - vl)
      (input + BitVec.ofNat 64 vl) (output + BitVec.ofNat 64 vl) p := by
  constructor <;> simp [rvvAfter, update, h.min, h.max]

/-- Total correctness of the exact extracted RVV loop, for every size_t-sized
length and every progressing, bounded VL schedule. The postcondition specifies
all memory, including the frame, rather than only the output byte list. -/
theorem rvv_loop_total (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : Params) (locals : RvvLocals s n input output p) (bound : n < 2^64)
    (safe : RegionSafe s.memory input output n) :
    ∃ t, Exec cfg rvvLoop s t ∧
      t.memory = writeBytes s.memory output ((readBytes s.memory input n).map (mainLane p)) := by
  by_cases zero : n = 0
  · subst n
    refine ⟨s, ?_, rfl⟩
    apply Exec.done (v := .integer 0)
    · simp [rvvLoop, firstStatement, dropStatements, Generated.S8Clamp.rvv,
        eval, binary, convert, locals.batch]
    · rfl
  · let k := cfg.choose n
    have pos : 0 < k := cfg.positive n (by omega)
    have le : k ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
    let bs := readBytes s.memory input k
    let written := bs.map (mainLane p)
    let m := writeBytes s.memory output written
    let next := rvvAfter s n k input output written m
    have len : written.length = k := by simp [written, bs]
    have load : loadBytes s.memory input k = some bs :=
      loadBytes_success _ _ _ (fun a ha => safe.readable a (footprint_mono le ha))
    have store : storeBytes s.memory output written = some m :=
      storeBytes_success _ _ _ (fun a ha => safe.writable a (footprint_mono (by omega) ha))
    have body : Exec cfg rvvBody s next := rvv_body_exec cfg s n input output p bs m
      locals bound (readBytes_length ..) load store
    have nextlocals := rvvAfter_locals s n k input output p written m locals
    have nextsafe := safe.advance le written len
    obtain ⟨t, hrun, hmem⟩ := rvv_loop_total cfg next (n - k)
      (input + BitVec.ofNat 64 k) (output + BitVec.ofNat 64 k) p nextlocals (by omega) nextsafe
    refine ⟨t, ?_, ?_⟩
    · apply Exec.more (v := .integer 1) (t := next)
      · simp [rvvLoop, firstStatement, dropStatements, Generated.S8Clamp.rvv,
          eval, binary, convert, locals.batch, zero, show (0 : Int) < n by omega]
      · rfl
      · exact body
      · exact hrun
    · rw [hmem]
      change writeBytes m (output + BitVec.ofNat 64 k)
        ((readBytes m (input + BitVec.ofNat 64 k) (n - k)).map (mainLane p)) = _
      rw [safe.remaining_read le written len]
      have split : n = k + (n - k) := by omega
      conv => rhs; rw [split, readBytes_add, List.map_append, writeBytes_append]
      simp only [List.length_map, readBytes_length]
      rfl
termination_by n

structure NeonLocals (s : State) (n : Nat) (input output : Address) (p : Params) : Prop where
  batch : s.locals "batch" = some (.integer n)
  inputPtr : s.locals "input" = some (.pointer input)
  outputPtr : s.locals "output" = some (.pointer output)
  min : s.locals "voutput_min" = some (.vector 1 (List.replicate 16 p.lo))
  max : s.locals "voutput_max" = some (.vector 1 (List.replicate 16 p.hi))

theorem zip_replicate (f : Byte → Byte → Byte) (bs : List Byte) (x : Byte) (n : Nat) :
    List.zipWith f bs (List.replicate n x) = (bs.take n).map (fun b => f b x) := by
  induction bs generalizing n with
  | nil => simp
  | cons b bs ih => cases n <;> simp [List.replicate_succ, ih]

private theorem zip8 (f : Byte → Byte → Byte) (bs : List Byte) (x : Byte) :
    List.zipWith f bs [x,x,x,x,x,x,x,x] = (bs.take 8).map (fun b => f b x) :=
  zip_replicate f bs x 8

def neon8After (s : State) (n : Nat) (input output : Address) (bytes : List Byte)
    (m : Memory) : State :=
  let t := update s "input" (.pointer (input + 8))
  let t := update t "vacc" (.vector 1 bytes)
  let t := { t with memory := m }
  let t := update t "output" (.pointer (output + 8))
  update t "batch" (.integer (n - 8 : Nat))

/-- The 8-byte source path keeps its original min-then-max order. Equating it
with the RVV order requires the separately proved ordered-bound lemma. -/
theorem neon8_body_exec (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : Params) (bs : List Byte) (m : Memory)
    (locals : NeonLocals s n input output p) (bound : n < 2^64) (large : 8 ≤ n)
    (hlen : bs.length = 8)
    (hload : loadBytes s.memory input 8 = some bs)
    (hstore : storeBytes s.memory output (bs.map (tailLane p)) = some m) :
    Exec cfg neon8Body s (neon8After s n input output (bs.map (tailLane p)) m) := by
  have ht (f : Byte → Byte) : (bs.map f).take 8 = bs.map f := by
    apply List.take_of_length_le
    simp [hlen]
  have ht0 : bs.take 8 = bs := by apply List.take_of_length_le; omega
  have hs : storeBytes s.memory output
      (bs.map (fun x => ByteISA.maxSigned (ByteISA.minSigned x p.hi) p.lo)) = some m := hstore
  apply run_sound (fuel := 20)
  simp +contextual [neon8Body, loopBody, firstStatement, dropStatements, Generated.S8Clamp.neon,
    run, eval, intrinsic, zipLanes, effect, storeVector, update, locals.batch,
    locals.inputPtr, locals.outputPtr, locals.min, locals.max, hlen, hload, hstore,
    neon8After, binary, ht, ht0, hs, tailLane, zip_replicate, List.map_map, Function.comp_def,
    cast_sub n 8 large bound, show convert .u64 8 = 8 from cast_nat 8 (by decide), zip8]
  have hsub : convert .u64 ((n : Int) - 8) = (n - 8 : Nat) := by
    simpa using cast_sub n 8 large bound
  simp only [hsub]
  rfl

end Salty.Kernels.S8Clamp.Execution
