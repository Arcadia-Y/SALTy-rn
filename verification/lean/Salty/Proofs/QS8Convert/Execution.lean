import Salty.Proofs.Core.CByteSyntax
import Salty.Proofs.Core.CByteMemory
import Salty.Generated.QS8ConvertNeon
import Salty.Generated.QS8ConvertRvv
import Salty.Proofs.S8Clamp.Execution

/-! Instruction and block execution lemmas for the extracted qs8-vcvt programs.
The complete guarantees are exposed in `Salty.Results.QS8Convert`. -/
namespace Salty.Kernels.QS8Convert
open CByte QuantizedISA
open SIMD.Signed

def rvvLoop : Stmt := firstStatement (dropStatements 7 Generated.QS8Convert.rvv)
def rvvBody : Stmt := loopBody rvvLoop

structure RvvLocals (s : State) (n : Nat) (input output : Address) (p : Params) : Prop where
  batch : s.locals "batch" = some (.integer n)
  inputPtr : s.locals "input" = some (.pointer input)
  outputPtr : s.locals "output" = some (.pointer output)
  inputZero : s.locals "input_zero_point" = some (.integer p.inputZero.toInt)
  multiplier : s.locals "multiplier" = some (.integer p.multiplier.toInt)
  outputZero : s.locals "output_zero_point" = some (.integer p.outputZero.toInt)

def rvvProduct (p : Params) (x : Byte) : BitVec 32 :=
  wideningMul16 (shift16 (reverseSub16 (signExtend8 x) p.inputZero) 7) p.multiplier

def rvvAccumulator (p : Params) (x : Byte) : BitVec 16 :=
  addSat16 (clipRNU15 (rvvProduct p x)) p.outputZero

def rvvAfter (s : State) (n vl : Nat) (input output : Address) (p : Params)
    (bs : List Byte) (m : Memory) : State :=
  let t := update s "vl" (.integer vl)
  let t := update t "vx" (.vector 1 bs)
  let t := update t "vx_w" (.halfwords (bs.map signExtend8))
  let t := update t "prod" (.words32 (bs.map (rvvProduct p)))
  let t := update t "vacc" (.halfwords (bs.map (rvvAccumulator p)))
  let t := update t "vy" (.vector 1 (bs.map (rvvLane p)))
  let t := { t with memory := m }
  let t := update t "input" (.pointer (input + BitVec.ofNat 64 vl))
  let t := update t "output" (.pointer (output + BitVec.ofNat 64 vl))
  update t "batch" (.integer (n - vl : Nat))

set_option maxHeartbeats 1000000 in
theorem rvv_body_exec (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : Params) (bs : List Byte) (m : Memory)
    (locals : RvvLocals s n input output p) (bound : n < 2^64)
    (hlen : bs.length = cfg.choose n)
    (hload : loadBytes s.memory input (cfg.choose n) = some bs)
    (hstore : storeBytes s.memory output (bs.map (rvvLane p)) = some m) :
    Exec cfg rvvBody s (rvvAfter s n (cfg.choose n) input output p bs m) := by
  have hvn : cfg.choose n ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
  have hvc : cfg.choose n ≤ cfg.capacity := Nat.le_trans (cfg.bounded n) (Nat.min_le_right ..)
  have ht {α : Type} (f : Byte → α) : (bs.map f).take (cfg.choose n) = bs.map f := by
    apply List.take_of_length_le
    simp [hlen]
  have ht0 : bs.take (cfg.choose n) = bs := by simp [← hlen]
  have c7 : convert .u64 7 = 7 := rfl
  have c15 : convert .u64 15 = 15 := rfl
  have c0 : convert .u64 0 = 0 := rfl
  have r0 : convert .u32 0 = 0 := rfl
  have r2 : convert .u32 2 = 2 := rfl
  have hs : storeBytes s.memory output (bs.map (fun x => clipRDN0
      (addSat16 (clipRNU15 (wideningMul16
        (shift16 (reverseSub16 (signExtend8 x) p.inputZero) 7) p.multiplier))
        p.outputZero))) = some m := hstore
  apply run_sound (fuel := 24)
  simp +contextual (maxSteps := 1000000) [rvvBody, rvvLoop, loopBody, firstStatement, dropStatements,
    Generated.QS8Convert.rvv, run, eval, intrinsic, saturatingIntrinsic, effect, update,
    locals.batch, locals.inputPtr, locals.outputPtr, locals.inputZero, locals.multiplier,
    locals.outputZero, hlen, hload, hs, hvc, hvn, c7, c15, c0, r0, r2, cast_sub n _ hvn bound,
    rvvAfter, binary, ht, ht0, rvvLane, rvvProduct, rvvAccumulator,
    List.map_map, Function.comp_def]
  rfl

theorem rvvAfter_locals (s : State) (n vl : Nat) (input output : Address) (p : Params)
    (bs : List Byte) (m : Memory) (h : RvvLocals s n input output p) :
    RvvLocals (rvvAfter s n vl input output p bs m) (n - vl)
      (input + BitVec.ofNat 64 vl) (output + BitVec.ofNat 64 vl) p := by
  constructor <;> simp [rvvAfter, update, h.inputZero, h.multiplier, h.outputZero]

/-- Total correctness of the exact extracted RVV loop, for every size_t-sized
length and every progressing, bounded VL schedule. The postcondition specifies
all memory, including the frame, rather than only the output byte list. -/
theorem rvv_loop_total (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : Params) (locals : RvvLocals s n input output p) (bound : n < 2^64)
    (safe : S8Clamp.Execution.RegionSafe s.memory input output n) :
    ∃ t, Exec cfg rvvLoop s t ∧
      t.memory = writeBytes s.memory output ((readBytes s.memory input n).map (rvvLane p)) := by
  by_cases zero : n = 0
  · subst n
    refine ⟨s, ?_, rfl⟩
    apply Exec.done (v := .integer 0)
    · simp [rvvLoop, firstStatement, dropStatements, Generated.QS8Convert.rvv,
        eval, binary, convert, locals.batch]
    · rfl
  · let k := cfg.choose n
    have pos : 0 < k := cfg.positive n (by omega)
    have le : k ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
    let bs := readBytes s.memory input k
    let written := bs.map (rvvLane p)
    let m := writeBytes s.memory output written
    let next := rvvAfter s n k input output p bs m
    have len : written.length = k := by simp [written, bs]
    have load : loadBytes s.memory input k = some bs :=
      loadBytes_success _ _ _ (fun a ha => safe.readable a (footprint_mono le ha))
    have store : storeBytes s.memory output written = some m :=
      storeBytes_success _ _ _ (fun a ha => safe.writable a (footprint_mono (by omega) ha))
    have body : Exec cfg rvvBody s next := rvv_body_exec cfg s n input output p bs m
      locals bound (readBytes_length ..) load store
    have nextlocals := rvvAfter_locals s n k input output p bs m locals
    have nextsafe := safe.advance le written len
    obtain ⟨t, hrun, hmem⟩ := rvv_loop_total cfg next (n - k)
      (input + BitVec.ofNat 64 k) (output + BitVec.ofNat 64 k) p nextlocals (by omega) nextsafe
    refine ⟨t, ?_, ?_⟩
    · apply Exec.more (v := .integer 1) (t := next)
      · simp [rvvLoop, firstStatement, dropStatements, Generated.QS8Convert.rvv,
          eval, binary, convert, locals.batch, zero, show (0 : Int) < n by omega]
      · rfl
      · exact body
      · exact hrun
    · rw [hmem]
      change writeBytes m (output + BitVec.ofNat 64 k)
        ((readBytes m (input + BitVec.ofNat 64 k) (n - k)).map (rvvLane p)) = _
      rw [safe.remaining_read le written len]
      have split : n = k + (n - k) := by omega
      conv => rhs; rw [split, readBytes_add, List.map_append, writeBytes_append]
      simp only [List.length_map, readBytes_length]
      rfl
termination_by n

def neon8Loop : Stmt := firstStatement (dropStatements 7 Generated.QS8Convert.neon)
def neon8Body : Stmt := loopBody neon8Loop

structure NeonLocals (s : State) (n : Nat) (input output : Address) (p : Params) : Prop where
  batch : s.locals "batch" = some (.integer n)
  inputPtr : s.locals "input" = some (.pointer input)
  outputPtr : s.locals "output" = some (.pointer output)
  inputZero : s.locals "vinput_zero_point" = some (.halfwords (List.replicate 8 p.inputZero))
  multiplier : s.locals "vmultiplier" = some (.halfwords (List.replicate 8 p.multiplier))
  outputZero : s.locals "voutput_zero_point" = some (.halfwords (List.replicate 8 p.outputZero))

theorem zip_replicate_right {α β γ : Type} (f : α → β → γ) (bs : List α) (x : β) (n : Nat) :
    List.zipWith f bs (List.replicate n x) = (bs.take n).map (fun b => f b x) := by
  induction bs generalizing n with
  | nil => simp
  | cons b bs ih => cases n <;> simp [List.replicate_succ, ih]

theorem zip_replicate_left {α β γ : Type} (f : α → β → γ) (x : α) (bs : List β) (n : Nat) :
    List.zipWith f (List.replicate n x) bs = (bs.take n).map (f x) := by
  induction bs generalizing n with
  | nil => simp
  | cons b bs ih => cases n <;> simp [List.replicate_succ, ih]

def neonAccumulator (p : Params) (x : Byte) : BitVec 16 :=
  addSat16 (SIMD.Signed.sqrdmulh16 (shift16 (subWide8 p.inputZero x) 7) p.multiplier) p.outputZero

def neon8After (s : State) (n : Nat) (input output : Address) (p : Params)
    (bs : List Byte) (m : Memory) : State :=
  let t := update s "vx" (.vector 1 bs)
  let t := update t "input" (.pointer (input + 8))
  let t := update t "vacc" (.halfwords (bs.map (neonAccumulator p)))
  let t := update t "vy" (.vector 1 (bs.map (neonLane p)))
  let t := { t with memory := m }
  let t := update t "output" (.pointer (output + 8))
  update t "batch" (.integer (n - 8 : Nat))

set_option maxHeartbeats 1000000 in
theorem neon8_body_exec (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : Params) (bs : List Byte) (m : Memory)
    (locals : NeonLocals s n input output p) (bound : n < 2^64) (large : 8 ≤ n)
    (hlen : bs.length = 8) (hload : loadBytes s.memory input 8 = some bs)
    (hstore : storeBytes s.memory output (bs.map (neonLane p)) = some m) :
    Exec cfg neon8Body s (neon8After s n input output p bs m) := by
  have ht {α : Type} (f : Byte → α) : (bs.map f).take 8 = bs.map f := by
    apply List.take_of_length_le
    simp [hlen]
  have ht0 : bs.take 8 = bs := by simp [← hlen]
  have zr {α β γ : Type} (f : α → β → γ) (xs : List α) (x : β) :
      List.zipWith f xs [x,x,x,x,x,x,x,x] = (xs.take 8).map (fun b => f b x) :=
    zip_replicate_right f xs x 8
  have zl {α β γ : Type} (f : α → β → γ) (x : α) (xs : List β) :
      List.zipWith f [x,x,x,x,x,x,x,x] xs = (xs.take 8).map (f x) :=
    zip_replicate_left f x xs 8
  have c8 : convert .u64 8 = 8 := rfl
  have hs : storeBytes s.memory output (bs.map (fun x => narrowSat8
      (addSat16 (SIMD.Signed.sqrdmulh16 (shift16 (subWide8 p.inputZero x) 7)
        p.multiplier) p.outputZero))) = some m := hstore
  apply run_sound (fuel := 24)
  simp +contextual (maxSteps := 1000000) [neon8Body, neon8Loop, loopBody,
    firstStatement, dropStatements, Generated.QS8Convert.neon, run, eval, intrinsic,
    saturatingIntrinsic, effect, storeVector, update, locals.batch, locals.inputPtr,
    locals.outputPtr, locals.inputZero, locals.multiplier, locals.outputZero,
    hlen, hload, hs, c8, cast_sub n 8 large bound, neon8After, binary, ht, ht0,
    zr, zl, neonLane, neonAccumulator, List.map_map, Function.comp_def]
  have hsub : convert .u64 ((n : Int) - 8) = (n - 8 : Nat) := by
    simpa using cast_sub n 8 large bound
  simp only [hsub]
  rfl

end Salty.Kernels.QS8Convert
