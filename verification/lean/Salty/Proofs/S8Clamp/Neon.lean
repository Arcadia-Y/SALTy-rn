import Salty.Spec.ByteRegions
import Salty.Proofs.S8Clamp.Neon64
import Salty.Proofs.S8Clamp.Tail

namespace Salty.Kernels.S8Clamp.Execution
open CByte

theorem PaddedSafe.region {m : Memory} {input output : Address} {n : Nat}
    (h : PaddedSafe m input output n) : RegionSafe m input output n where
  readable a ha := h.readable a (footprint_mono (by omega) ha)
  writable := h.writable
  separate a ha := h.separate a (footprint_mono (by omega) ha)

theorem PaddedSafe.advance {m : Memory} {input output : Address} {n k : Nat}
    (safe : PaddedSafe m input output n) (hk : k ≤ n) (bs : List Byte) (hlen : bs.length = k) :
    PaddedSafe (writeBytes m output bs) (input + BitVec.ofNat 64 k)
      (output + BitVec.ofNat 64 k) (n - k) := by
  have sum : k + (n - k) = n := by omega
  have sum7 : k + (n - k + 7) = n + 7 := by omega
  constructor
  · intro a ha
    rw [writeBytes_readable]
    apply safe.readable a
    simpa only [sum7] using footprint_shift input a (n - k + 7) k ha
  · intro a ha
    rw [writeBytes_writable]
    apply safe.writable a
    simpa only [sum] using footprint_shift output a (n - k) k ha
  · intro a hi ho
    apply safe.separate a
    · simpa only [sum7] using footprint_shift input a (n - k + 7) k hi
    · simpa only [sum] using footprint_shift output a (n - k) k ho

def neon8Loop : Stmt := firstStatement (dropStatements 7 Generated.S8Clamp.neon)
def neon8AndTail : Stmt := dropStatements 7 Generated.S8Clamp.neon

theorem neon8AndTail_shape : neon8AndTail = .seq neon8Loop (.seq neonTail .skip) := rfl

theorem neon8After_locals (s : State) (n : Nat) (input output : Address) (p : Params)
    (bs : List Byte) (m : Memory) (h : NeonLocals s n input output p) :
    NeonLocals (neon8After s n input output bs m) (n - 8) (input + 8) (output + 8) p := by
  constructor <;> simp [neon8After, update, h.min, h.max]

/-- Complete extracted 8-byte loop followed by the extracted padded tail. -/
theorem neon8_tail_total (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : Params) (valid : Valid p) (locals : NeonLocals s n input output p)
    (bound : n < 2^64) (safe : PaddedSafe s.memory input output n) :
    ∃ t, Exec cfg neon8AndTail s t ∧
      t.memory = writeBytes s.memory output ((readBytes s.memory input n).map (mainLane p)) := by
  have lane : tailLane p = mainLane p := funext (clamp_order p valid)
  by_cases small : n < 8
  · obtain ⟨t, htail, hm⟩ := neon_tail_total cfg s n input output p locals small
      (fun hn a ha => safe.readable a (footprint_mono (by omega) ha)) safe.writable
    refine ⟨t, ?_, by simpa only [lane] using hm⟩
    rw [neon8AndTail_shape]
    apply Exec.seq (t := s)
    · apply Exec.done (v := .integer 0)
      · simp [neon8Loop, firstStatement, dropStatements, Generated.S8Clamp.neon,
          eval, binary, convert, Int.max_def, locals.batch, show ¬ (8 : Int) ≤ n by omega]
      · rfl
    · exact .seq htail .skip
  · have large : 8 ≤ n := by omega
    let bs := readBytes s.memory input 8
    let written := bs.map (mainLane p)
    let m := writeBytes s.memory output written
    let next := neon8After s n input output written m
    have len : written.length = 8 := by simp [written, bs]
    have load : loadBytes s.memory input 8 = some bs :=
      loadBytes_success _ _ _ (fun a ha => safe.readable a (footprint_mono (by omega) ha))
    have store : storeBytes s.memory output written = some m :=
      storeBytes_success _ _ _ (fun a ha => safe.writable a (footprint_mono (by omega) ha))
    have body : Exec cfg neon8Body s next := by
      simpa only [lane] using neon8_body_exec cfg s n input output p bs m locals bound large
        (readBytes_length ..) load (by simpa only [lane] using store)
    have nextlocals := neon8After_locals s n input output p written m locals
    have nextsafe : PaddedSafe next.memory (input + 8) (output + 8) (n - 8) := by
      simpa using safe.advance large written len
    obtain ⟨t, hrun, hm⟩ := neon8_tail_total cfg next (n - 8) (input + 8) (output + 8)
      p valid nextlocals (by omega) nextsafe
    refine ⟨t, ?_, ?_⟩
    · rw [neon8AndTail_shape] at hrun ⊢
      cases hrun with
      | seq hloop htail =>
        apply Exec.seq (Exec.more (v := .integer 1) ?_ rfl body hloop) htail
        simp [neon8Loop, firstStatement, dropStatements, Generated.S8Clamp.neon,
          eval, binary, convert, Int.max_def, locals.batch, show (8 : Int) ≤ n by omega]
    · rw [hm]
      change writeBytes m (output + 8)
        ((readBytes m (input + 8) (n - 8)).map (mainLane p)) = _
      have remaining := safe.region.remaining_read large written len
      have remaining' : readBytes m (input + 8) (n - 8) = readBytes s.memory (input + 8) (n - 8) := by
        simpa using remaining
      rw [remaining']
      have split : n = 8 + (n - 8) := by omega
      conv => rhs; rw [split, readBytes_add, List.map_append, writeBytes_append]
      simp only [List.length_map, readBytes_length]
      rfl
termination_by n

theorem PaddedSafe.read_block {m : Memory} {input output : Address} {n : Nat}
    (safe : PaddedSafe m input output n) (offset width : Nat) (bound : offset + width ≤ n + 7) :
    loadBytes m (input + BitVec.ofNat 64 offset) width =
      some (readBytes m (input + BitVec.ofNat 64 offset) width) := by
  apply loadBytes_success
  intro a ha
  exact safe.readable a (footprint_mono bound (footprint_shift _ _ _ _ ha))

theorem PaddedSafe.write_block {m other : Memory} {input output : Address} {n : Nat}
    (safe : PaddedSafe m input output n) (same : other.writable = m.writable)
    (offset : Nat) (bs : List Byte) (bound : offset + bs.length ≤ n) :
    storeBytes other (output + BitVec.ofNat 64 offset) bs =
      some (writeBytes other (output + BitVec.ofNat 64 offset) bs) := by
  apply storeBytes_success
  intro a ha
  rw [same]
  exact safe.writable a (footprint_mono bound (footprint_shift _ _ _ _ ha))

/-- Safety and full-memory refinement of the extracted 64-byte body. All four
loads refer to the initial memory, just as in the source. -/
theorem neon64_safe (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : Params) (locals : NeonLocals s n input output p) (bound : n < 2^64)
    (large : 64 ≤ n) (safe : PaddedSafe s.memory input output n) :
    ∃ t, Exec cfg neon64Body s t ∧ NeonLocals t (n - 64) (input + 64) (output + 64) p ∧
      t.memory = writeBytes s.memory output ((readBytes s.memory input 64).map (mainLane p)) := by
  let b0 := readBytes s.memory input 16
  let c0 := b0.map (mainLane p)
  let m1 := writeBytes s.memory output c0
  have load0 : loadBytes s.memory input 16 = some b0 := by
    simpa [b0] using safe.read_block 0 16 (by omega)
  have store0 : storeBytes s.memory output c0 = some m1 := by
    simpa using safe.write_block (rfl) 0 c0 (by simp [c0, b0]; omega)
  let b1 := readBytes s.memory (input + 16#64) 16
  let c1 := b1.map (mainLane p)
  let m2 := writeBytes m1 (output + 16#64) c1
  have load1 : loadBytes s.memory (input + 16#64) 16 = some b1 := by
    simpa [b1] using safe.read_block 16 16 (by omega)
  have store1 : storeBytes m1 (output + 16#64) c1 = some m2 := by
    simpa using safe.write_block (by simp [m1]) 16 c1 (by simp [c1, b1]; omega)
  let b2 := readBytes s.memory (input + 32#64) 16
  let c2 := b2.map (mainLane p)
  let m3 := writeBytes m2 (output + 32#64) c2
  have load2 : loadBytes s.memory (input + 32#64) 16 = some b2 := by
    simpa [b2] using safe.read_block 32 16 (by omega)
  have store2 : storeBytes m2 (output + 32#64) c2 = some m3 := by
    simpa using safe.write_block (by simp [m1, m2]) 32 c2 (by simp [c2, b2]; omega)
  let b3 := readBytes s.memory (input + 48#64) 16
  let c3 := b3.map (mainLane p)
  let m4 := writeBytes m3 (output + 48#64) c3
  have load3 : loadBytes s.memory (input + 48#64) 16 = some b3 := by
    simpa [b3] using safe.read_block 48 16 (by omega)
  have store3 : storeBytes m3 (output + 48#64) c3 = some m4 := by
    simpa using safe.write_block (by simp [m1, m2, m3]) 48 c3 (by simp [c3, b3]; omega)
  let t := neon64After s n input output p b0 b1 b2 b3 m1 m2 m3 m4
  refine ⟨t, ?_, neon64After_locals s n input output p b0 b1 b2 b3 m1 m2 m3 m4 locals, ?_⟩
  · exact neon64_body_exec cfg s n input output p b0 b1 b2 b3 m1 m2 m3 m4 locals bound large
      (readBytes_length ..) load0 (readBytes_length ..) load1
      (readBytes_length ..) load2 (readBytes_length ..) load3 store0 store1 store2 store3
  · change m4 = _
    have split : readBytes s.memory input 64 = b0 ++ b1 ++ b2 ++ b3 := by
      rw [show 64 = 32 + 32 from rfl, readBytes_add,
        show 32 = 16 + 16 from rfl, readBytes_add, readBytes_add]
      simp [b0, b1, b2, b3, BitVec.add_assoc, List.append_assoc]
    rw [split]
    simp [List.map_append, writeBytes_append, m4, m3, m2, m1, c0, c1, c2, c3,
      b0, b1, b2, b3, BitVec.add_assoc]

def neon64Loop : Stmt := firstStatement (dropStatements 6 Generated.S8Clamp.neon)
def neonSuffix : Stmt := dropStatements 6 Generated.S8Clamp.neon

theorem neonSuffix_shape : neonSuffix = .seq neon64Loop neon8AndTail := rfl

/-- Total correctness of all extracted source loops and its padded tail, from
initialized vector bounds. This still excludes the function's initialization. -/
theorem neon_suffix_total (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : Params) (valid : Valid p) (locals : NeonLocals s n input output p)
    (bound : n < 2^64) (safe : PaddedSafe s.memory input output n) :
    ∃ t, Exec cfg neonSuffix s t ∧
      t.memory = writeBytes s.memory output ((readBytes s.memory input n).map (mainLane p)) := by
  by_cases small : n < 64
  · obtain ⟨t, htail, hm⟩ := neon8_tail_total cfg s n input output p valid locals bound safe
    refine ⟨t, ?_, hm⟩
    rw [neonSuffix_shape]
    apply Exec.seq (t := s) ?_ htail
    apply Exec.done (v := .integer 0)
    · simp [neon64Loop, firstStatement, dropStatements, Generated.S8Clamp.neon,
        eval, binary, convert, Int.max_def, locals.batch, show ¬ (64 : Int) ≤ n by omega]
    · rfl
  · have large : 64 ≤ n := by omega
    obtain ⟨next, hbody, nextlocals, nextmem⟩ := neon64_safe cfg s n input output p locals bound large safe
    let written := (readBytes s.memory input 64).map (mainLane p)
    have len : written.length = 64 := by simp [written]
    have nextsafe : PaddedSafe next.memory (input + 64) (output + 64) (n - 64) := by
      rw [nextmem]
      simpa using safe.advance large written len
    obtain ⟨t, hrun, hm⟩ := neon_suffix_total cfg next (n - 64) (input + 64) (output + 64)
      p valid nextlocals (by omega) nextsafe
    refine ⟨t, ?_, ?_⟩
    · rw [neonSuffix_shape] at hrun ⊢
      cases hrun with
      | seq hloop htail =>
        apply Exec.seq (Exec.more (v := .integer 1) ?_ rfl hbody hloop) htail
        simp [neon64Loop, firstStatement, dropStatements, Generated.S8Clamp.neon,
          eval, binary, convert, Int.max_def, locals.batch, show (64 : Int) ≤ n by omega]
    · rw [hm, nextmem]
      have remaining : readBytes (writeBytes s.memory output written) (input + 64) (n - 64) =
          readBytes s.memory (input + 64) (n - 64) := by
        simpa using safe.region.remaining_read large written len
      rw [remaining]
      have split : n = 64 + (n - 64) := by omega
      conv => rhs; rw [split, readBytes_add, List.map_append, writeBytes_append]
      simp only [List.length_map, readBytes_length]
      rfl
termination_by n

end Salty.Kernels.S8Clamp.Execution
