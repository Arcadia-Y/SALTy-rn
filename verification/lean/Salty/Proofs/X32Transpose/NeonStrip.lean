import Salty.Proofs.X32Transpose.NeonSafety

namespace Salty.Kernels.X32Transpose
open CByte

def neonColumn1 (p : MatrixCopy) : Address :=
  if p.cols = 1 then p.output else p.output + BitVec.ofNat 64 p.outputStride

/-- The C size_t multiplication wraps before the pointer updates use it. -/
def neonInputOffset (p : MatrixCopy) : Nat := (BitVec.ofNat 64 (2*p.inputStride)).toNat

theorem neonInputOffset_cast (p : MatrixCopy) :
    convert .u64 (2 * (p.inputStride : Int)) = (neonInputOffset p : Int) := by
  change ((BitVec.ofInt 64 ((2 : Nat) * (p.inputStride : Int))).toNat : Int) = _
  simp only [convert, neonInputOffset, ← Int.natCast_mul, BitVec.ofInt_natCast]

abbrev NeonStripLocals (s : State) (p : MatrixCopy) : Prop :=
  NeonRowLocals s p.rows (neonInputOffset p) p.input (p.input + BitVec.ofNat 64 p.inputStride)
    p.output (neonColumn1 p)

/-- Execute one actual pair of source rows and identify the complete memory
with the same row-slice specification used to compose the full transpose. -/
theorem neon_pair_total (cfg : Config) (s : State) (p : MatrixCopy)
    (locals : NeonStripLocals s p) (width : p.cols = 1 ∨ p.cols = 2)
    (height : 2 ≤ p.rows) (bound : p.rows < 2^64)
    (safe : NeonStripSafe s.memory p) (sep : p.separated) :
    ∃ t, Exec cfg neonRowBody s t ∧ t.memory = (p.rowSlice 0 2).result s.memory ∧
      NeonStripLocals t (p.rowSlice 2 (p.rows-2)) := by
  let i1 := p.input + BitVec.ofNat 64 p.inputStride
  let o1 := neonColumn1 p
  let a := readBytes s.memory p.input 4
  let b := readBytes s.memory (p.input + 4#64) 4
  let c := readBytes s.memory i1 4
  let d := readBytes s.memory (i1 + 4#64) 4
  let m1 := writeBytes s.memory o1 (b ++ d)
  let m2 := writeBytes m1 p.output (a ++ c)
  have load0 : loadBytes s.memory p.input 8 = some (a ++ b) := by
    rw [loadBytes_success _ _ _ (fun addr hp => safe.padded 0 (by omega) addr (by simpa [rowAddress] using hp))]
    exact congrArg some (readBytes_add s.memory p.input 4 4)
  have load1 : loadBytes s.memory i1 8 = some (c ++ d) := by
    rw [loadBytes_success _ _ _ (fun addr hp => safe.padded 1 (by omega) addr (by simpa [rowAddress, i1] using hp))]
    exact congrArg some (readBytes_add s.memory i1 4 4)
  have out0 : ∀ addr, Footprint p.output 8 addr → s.memory.writable addr = true := by
    intro addr hp
    apply safe.store_pair 0 (by omega) height addr
    simpa [MatrixCopy.writeAddress] using hp
  have out1 : ∀ addr, Footprint o1 8 addr → s.memory.writable addr = true := by
    intro addr hp
    rcases width with one | two
    · exact out0 addr (by simpa [o1, neonColumn1, one] using hp)
    · apply safe.store_pair 1 (by omega) height addr
      simpa [o1, neonColumn1, two, MatrixCopy.writeAddress] using hp
  have hs1 : storeBytes s.memory o1 (b ++ d) = some m1 := by
    apply storeBytes_success
    simpa [b, d] using out1
  have hs0 : storeBytes m1 p.output (a ++ c) = some m2 := by
    apply storeBytes_success
    simpa [m1, a, c] using out0
  let t := neonRowAfter s p.rows (neonInputOffset p) p.input i1 p.output o1 a b c d m1 m2
  have he : Exec cfg neonRowBody s t := neon_row_exec cfg s p.rows (neonInputOffset p)
    p.input i1 p.output o1 a b c d m1 m2 locals height bound
    (readBytes_length ..) (readBytes_length ..) (readBytes_length ..) (readBytes_length ..) load0 load1 hs1 hs0
  refine ⟨t, he, ?_, ?_⟩
  · change neonPairMemory s.memory p.input i1 p.output o1 = _
    have sliceEq : p.rowSlice 0 2 = {p with rows := 2} := by simp [MatrixCopy.rowSlice]
    rw [sliceEq]
    rcases width with one | two
    · have result := neon_pair_matrix_alias s.memory p
      simpa only [i1, o1, neonColumn1, one, ↓reduceIte] using result
    · have tileSep := p.rowSlice_separated 0 2 (by omega) sep
      rw [sliceEq] at tileSep
      have result := neon_pair_matrix s.memory p (by simpa only [← two] using tileSep)
      simpa only [i1, o1, neonColumn1, two, Nat.reduceEqDiff, ↓reduceIte] using result
  · have hl := neonRowAfter_locals s p.rows (neonInputOffset p) p.input i1 p.output o1
      a b c d m1 m2 locals
    have hi : i1 + BitVec.ofNat 64 (neonInputOffset p) =
        (p.rowSlice 2 (p.rows-2)).input + BitVec.ofNat 64 p.inputStride := by
      simp only [i1, MatrixCopy.rowSlice, neonInputOffset, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      ac_rfl
    have ho : o1 + 8#64 = neonColumn1 (p.rowSlice 2 (p.rows-2)) := by
      by_cases one : p.cols = 1 <;> simp only [o1, neonColumn1, MatrixCopy.rowSlice,
        one, ↓reduceIte, Nat.reduceMul, BitVec.ofNat_eq_ofNat] <;> ac_rfl
    rw [hi, ho] at hl
    simpa only [neonInputOffset, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hl


def neonTailMemory (m : Memory) (p : MatrixCopy) : Memory :=
  writeBytes (writeBytes m (neonColumn1 p) (readBytes m (p.input + 4#64) 4))
    p.output (readBytes m p.input 4)

theorem neon_tail_matrix (m : Memory) (p : MatrixCopy)
    (width : p.cols = 1 ∨ p.cols = 2) (height : 0 < p.rows) (sep : p.separated) :
    neonTailMemory m p = (p.rowSlice 0 1).result m := by
  rcases width with one | two
  · simp only [neonTailMemory, neonColumn1, one, ↓reduceIte]
    rw [writeBytes_overwrite _ _ _ _ (by simp)]
    simp [MatrixCopy.result, MatrixCopy.rowVisits, MatrixCopy.rowSlice, MatrixCopy.writeWord,
      MatrixCopy.readAddress, MatrixCopy.writeAddress, one, List.range_succ]
  · have separate : ∀ a, Footprint (p.output + BitVec.ofNat 64 p.outputStride) 4 a →
        ¬ Footprint p.output 4 a := by
      intro a ha hb
      apply sep (0,1) (0,0) ⟨height,by omega⟩ ⟨height,by omega⟩ (by decide) a
      · simpa [MatrixCopy.writeAddress] using ha
      · simpa [MatrixCopy.writeAddress] using hb
    unfold neonTailMemory
    simp only [neonColumn1, two, Nat.reduceEqDiff, ↓reduceIte]
    rw [writeBytes_comm _ _ _ _ _ (by simpa only [readBytes_length] using separate)]
    simp [MatrixCopy.result, MatrixCopy.rowVisits, MatrixCopy.rowSlice, MatrixCopy.writeWord,
      MatrixCopy.readAddress, MatrixCopy.writeAddress, two, List.range_succ]

theorem neon_tail_locals_frame (cfg : Config) (s t : State) (p : MatrixCopy)
    (h : NeonStripLocals s p) (he : Exec cfg neonTail s t) : NeonStripLocals t p := by
  constructor
  · exact (he.locals_frame "bh" (by decide)).trans h.height
  · exact (he.locals_frame "i0" (by decide)).trans h.input0
  · exact (he.locals_frame "i1" (by decide)).trans h.input1
  · exact (he.locals_frame "o0" (by decide)).trans h.output0
  · exact (he.locals_frame "o1" (by decide)).trans h.output1
  · exact (he.locals_frame "input_offset" (by decide)).trans h.inputOffset
  · exact (he.locals_frame "tile_hbytes" (by decide)).trans h.outputOffset

theorem neon_last_row_total (cfg : Config) (s : State) (p : MatrixCopy)
    (locals : NeonStripLocals s p) (width : p.cols = 1 ∨ p.cols = 2) (height : p.rows = 1)
    (safe : NeonStripSafe s.memory p) (sep : p.separated) :
    ∃ t, Exec cfg neonTail s t ∧ t.memory = p.result s.memory ∧ NeonStripLocals t p := by
  let a := readBytes s.memory p.input 4
  let b := readBytes s.memory (p.input + 4#64) 4
  let m1 := writeBytes s.memory (neonColumn1 p) b
  let m2 := writeBytes m1 p.output a
  have load : loadBytes s.memory p.input 8 = some (a ++ b) := by
    rw [loadBytes_success _ _ _ (fun addr hp => safe.padded 0 (by omega) addr (by simpa [rowAddress] using hp))]
    exact congrArg some (readBytes_add s.memory p.input 4 4)
  have out0 : ∀ addr, Footprint p.output 4 addr → s.memory.writable addr = true := by
    intro addr hp
    apply safe.common.writable 0 (by omega) addr
    exact matrix_write_footprint p 0 0 (by omega) addr (by simpa [MatrixCopy.writeAddress] using hp)
  have out1 : ∀ addr, Footprint (neonColumn1 p) 4 addr → s.memory.writable addr = true := by
    intro addr hp
    rcases width with one | two
    · exact out0 addr (by simpa [neonColumn1, one] using hp)
    · apply safe.common.writable 0 (by omega) addr
      exact matrix_write_footprint p 0 1 (by omega) addr (by simpa [neonColumn1, two, MatrixCopy.writeAddress] using hp)
  have hs1 : storeBytes s.memory (neonColumn1 p) b = some m1 := by
    apply storeBytes_success
    simpa [b] using out1
  have hs0 : storeBytes m1 p.output a = some m2 := by
    apply storeBytes_success
    simpa [m1, a] using out0
  let t := neonTailAfter s a b m2
  have ht : Exec cfg neonTail s t := neon_tail_one cfg s (neonInputOffset p) p.input
    (p.input + BitVec.ofNat 64 p.inputStride) p.output (neonColumn1 p) a b m1 m2
    (by simpa only [NeonStripLocals, height] using locals) (readBytes_length ..) (readBytes_length ..) load hs1 hs0
  refine ⟨t, ht, ?_, neon_tail_locals_frame cfg s t p locals ht⟩
  change neonTailMemory s.memory p = _
  have result := neon_tail_matrix s.memory p width (by omega) sep
  have same : p.rowSlice 0 1 = p := by
    simp only [MatrixCopy.rowSlice, Nat.zero_mul, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [← height]
  rw [same] at result
  exact result


/-- An entire source column strip: the actual unbounded pair loop followed by
its actual odd-row tail. Every read uses the evolving memory, and the proof
establishes equality with the original-input matrix result. -/
theorem neon_strip_total (cfg : Config) (s : State) (p : MatrixCopy)
    (locals : NeonStripLocals s p) (width : p.cols = 1 ∨ p.cols = 2)
    (bound : p.rows < 2^64) (safe : NeonStripSafe s.memory p) (sep : p.separated) :
    ∃ t, Exec cfg (.seq neonRows neonTail) s t ∧ t.memory = p.result s.memory ∧
      NeonStripLocals t (p.rowSlice (p.rows/2*2) (p.rows%2)) := by
  by_cases large : 2 ≤ p.rows
  · obtain ⟨u, hu, hm, hl⟩ := neon_pair_total cfg s p locals width large bound safe sep
    have hs : NeonStripSafe u.memory (p.rowSlice 2 (p.rows-2)) :=
      safe.rowSlice 2 (p.rows-2) (by omega)
        (by rw [hm]; exact MatrixCopy.result_readable ..)
        (by rw [hm]; exact MatrixCopy.result_writable ..)
    obtain ⟨t, ht, hmem, hlast⟩ := neon_strip_total cfg u (p.rowSlice 2 (p.rows-2)) hl width
      (by change p.rows-2 < 2^64; omega) hs (p.rowSlice_separated 2 (p.rows-2) (by omega) sep)
    refine ⟨t, ?_, ?_, ?_⟩
    · cases ht with
      | seq hloop htail =>
        apply Exec.seq (t := _) _ htail
        apply Exec.more (v := .integer 1) (t := u)
        · simp [neonRows, neonOuterBody, neonOuter, firstStatement, dropStatements,
            Generated.X32Transpose.neon, eval, binary, locals.height,
            show convert .u64 2 = 2 by decide, show (2 : Int) ≤ p.rows by omega]
        · rfl
        · exact hu
        · exact hloop
    · rw [hmem, hm]
      exact safe.common.prefix_remaining_rows_result 2 large
    · change NeonStripLocals t ((p.rowSlice 2 (p.rows-2)).rowSlice
        ((p.rows-2)/2*2) ((p.rows-2)%2)) at hlast
      rw [MatrixCopy.rowSlice_compose] at hlast
      have he : 2 + (p.rows-2)/2*2 = p.rows/2*2 := by omega
      have hr : (p.rows-2)%2 = p.rows%2 := by omega
      simpa only [he, hr] using hlast
  · have small : p.rows < 2 := by omega
    have done : Exec cfg neonRows s s := by
      apply Exec.done (v := .integer 0)
      · simp [neonRows, neonOuterBody, neonOuter, firstStatement, dropStatements,
          Generated.X32Transpose.neon, eval, binary, locals.height,
          show convert .u64 2 = 2 by decide, show (p.rows : Int) < 2 by omega]
      · rfl
    have same : p.rowSlice (p.rows/2*2) (p.rows%2) = p := by
      simp [Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small, MatrixCopy.rowSlice]
    by_cases zero : p.rows = 0
    · have tail := neon_tail_zero cfg s (by simpa only [zero] using locals.height)
      refine ⟨s, .seq done tail, ?_, ?_⟩
      · rw [p.result_rowFold, zero]
        rfl
      · rw [same]
        exact locals
    · obtain ⟨t, ht, hm, hl⟩ := neon_last_row_total cfg s p locals width (by omega) safe sep
      exact ⟨t, .seq done ht, hm, by simpa only [same] using hl⟩
termination_by p.rows
decreasing_by change p.rows-2 < p.rows; omega

end Salty.Kernels.X32Transpose
