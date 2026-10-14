import Salty.Proofs.X32Transpose.NeonStrip

namespace Salty.Kernels.X32Transpose
open CByte

def neonInputReset (p : MatrixCopy) : Int :=
  convert .u64 (8 - convert .u64 (p.rows/2*2*p.inputStride : Nat))

def neonOutputReset (p : MatrixCopy) : Int :=
  convert .u64 (convert .u64 (2*p.outputStride : Nat) - convert .u64 (p.rows/2*2*4 : Nat))

/-- Values fixed by the source initializer. Reset and stride products retain
size_t wrapping, including the intentional negative reset of a tall strip. -/
structure NeonConstants (s : State) (p : MatrixCopy) : Prop where
  height : s.locals "block_height" = some (.integer p.rows)
  inputStride : s.locals "input_stride" = some (.integer p.inputStride)
  outputStride : s.locals "output_stride" = some (.integer p.outputStride)
  tileWidth : s.locals "tile_width" = some (.integer 2)
  hbytes : s.locals "tile_hbytes" = some (.integer 8)
  offset : s.locals "input_offset" = some (.integer (neonInputOffset p))
  inputReset : s.locals "input_reset" = some (.integer (neonInputReset p))
  outputReset : s.locals "output_reset" = some (.integer (neonOutputReset p))

structure NeonColumnLocals (s : State) (p : MatrixCopy) (width : Nat) extends NeonConstants s p where
  width : s.locals "block_width" = some (.integer width)
  input0 : s.locals "i0" = some (.pointer p.input)
  input1 : s.locals "i1" = some (.pointer (p.input + BitVec.ofNat 64 p.inputStride))
  output0 : s.locals "o0" = some (.pointer p.output)
  output1 : s.locals "o1" = some (.pointer (p.output + BitVec.ofNat 64 p.outputStride))

theorem NeonColumnLocals.withCols {s : State} {p : MatrixCopy} {width : Nat}
    (h : NeonColumnLocals s p width) (cols : Nat) : NeonColumnLocals s {p with cols := cols} width :=
  ⟨⟨h.height, h.inputStride, h.outputStride, h.tileWidth, h.hbytes, h.offset,
    h.inputReset, h.outputReset⟩, h.width, h.input0, h.input1, h.output0, h.output1⟩

def neonActiveStrip (p : MatrixCopy) (width : Nat) : MatrixCopy :=
  {p with cols := if width < 2 then 1 else 2}

def neonColumnPrep : Stmt := takeStatements 2 neonOuterBody
def neonColumnPost : Stmt := dropStatements 4 neonOuterBody

def neonColumnPrepared (s : State) (p : MatrixCopy) (width : Nat) : State :=
  let t := if width < 2 then update s "o1" (.pointer p.output) else s
  update t "bh" (.integer p.rows)

theorem neon_column_prep_exec (cfg : Config) (s : State) (p : MatrixCopy) (width : Nat)
    (h : NeonColumnLocals s p width) : Exec cfg neonColumnPrep s (neonColumnPrepared s p width) := by
  have hb : Exec cfg (firstStatement neonColumnPrep) s
      (if width < 2 then update s "o1" (.pointer p.output) else s) := by
    by_cases small : width < 2
    · simp only [small, ↓reduceIte]
      apply Exec.yes (v := .integer 1)
      · simp [neonColumnPrep, takeStatements, neonOuterBody, neonOuter, firstStatement,
          dropStatements, Generated.X32Transpose.neon, eval, binary, h.width,
          show convert .u64 2 = 2 by decide, show (width : Int) < 2 by omega]
      · rfl
      · exact .seq (.assign (by simpa [eval] using h.output0)) .skip
    · simp only [small, ↓reduceIte]
      apply Exec.no (v := .integer 0)
      · simp [neonColumnPrep, takeStatements, neonOuterBody, neonOuter, firstStatement,
          dropStatements, Generated.X32Transpose.neon, eval, binary, h.width,
          show convert .u64 2 = 2 by decide, show ¬ (width : Int) < 2 by omega]
      · rfl
      · exact .skip
  have hh : (if width < 2 then update s "o1" (.pointer p.output) else s).locals "block_height" =
      some (.integer p.rows) := by split <;> simp [update, h.height]
  exact .seq hb (.seq (.assign (by simpa [eval] using hh)) .skip)

theorem neon_column_prepared_locals (s : State) (p : MatrixCopy) (width : Nat)
    (h : NeonColumnLocals s p width) :
    NeonStripLocals (neonColumnPrepared s p width) (neonActiveStrip p width) := by
  by_cases small : width < 2 <;> constructor <;>
    simp [NeonStripLocals, neonColumnPrepared, neonActiveStrip, neonColumn1, neonInputOffset,
      small, update, h.input0, h.input1, h.output0, h.output1, h.hbytes, h.offset,
      neonInputOffset] at *

theorem NeonConstants.frame {cfg : Config} {s t : State} {p : MatrixCopy}
    (h : NeonConstants s p) (he : Exec cfg (.seq neonRows neonTail) s t) : NeonConstants t p := by
  constructor
  · exact (he.locals_frame "block_height" (by decide)).trans h.height
  · exact (he.locals_frame "input_stride" (by decide)).trans h.inputStride
  · exact (he.locals_frame "output_stride" (by decide)).trans h.outputStride
  · exact (he.locals_frame "tile_width" (by decide)).trans h.tileWidth
  · exact (he.locals_frame "tile_hbytes" (by decide)).trans h.hbytes
  · exact (he.locals_frame "input_offset" (by decide)).trans h.offset
  · exact (he.locals_frame "input_reset" (by decide)).trans h.inputReset
  · exact (he.locals_frame "output_reset" (by decide)).trans h.outputReset

theorem pointer_reset (base : Address) (done next : Nat) :
    (base + BitVec.ofNat 64 done) +
      BitVec.ofInt 64 (convert .u64 (convert .u64 (next : Nat) - convert .u64 (done : Nat))) =
      base + BitVec.ofNat 64 next := by
  rw [cast_u64_word, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
    cast_u64_word, cast_u64_word]
  simp only [BitVec.ofInt_natCast]
  calc
    _ = (base + BitVec.ofNat 64 next) + (BitVec.ofNat 64 done + -BitVec.ofNat 64 done) := by ac_rfl
    _ = _ := by rw [BitVec.add_right_neg, BitVec.add_zero]


def neonColumnAfter (s : State) (p : MatrixCopy) (width : Nat) : State :=
  let t := update s "i0" (.pointer (p.input + 8#64))
  let t := update t "i1" (.pointer ((p.input + 8#64) + BitVec.ofNat 64 p.inputStride))
  let t := update t "o0" (.pointer (p.output + BitVec.ofNat 64 (2*p.outputStride)))
  let t := update t "o1" (.pointer (neonColumn1 (neonActiveStrip p width) + BitVec.ofNat 64 (2*p.outputStride)))
  update t "block_width" (.integer (width-2 : Nat))

theorem eval_pointer_add (cfg : Config) (s : State) (name offset : String)
    (a : Address) (n : Int) (ha : s.locals name = some (.pointer a))
    (hn : s.locals offset = some (.integer n)) :
    eval cfg s (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var name)) (.var offset)))) =
      some (.pointer (a + BitVec.ofInt 64 n)) := by
  simp only [eval, ha, hn, bind, pure, Option.bind, binary, pointer_integer_add]

theorem neon_column_post_exec (cfg : Config) (s : State) (p : MatrixCopy) (width : Nat)
    (h : NeonConstants s p) (hw : s.locals "block_width" = some (.integer width))
    (hl : NeonStripLocals s ((neonActiveStrip p width).rowSlice (p.rows/2*2) (p.rows%2))) :
    Exec cfg neonColumnPost s (neonColumnAfter s p width) := by
  have ir : (p.input + BitVec.ofNat 64 (p.rows/2*2*p.inputStride)) +
      BitVec.ofInt 64 (neonInputReset p) = p.input + 8#64 := by
    simpa only [neonInputReset, show convert .u64 (8 : Nat) = 8 by decide, BitVec.ofNat_eq_ofNat]
      using pointer_reset p.input (p.rows/2*2*p.inputStride) 8
  have outr (base : Address) : (base + BitVec.ofNat 64 (4*(p.rows/2*2))) +
      BitVec.ofInt 64 (neonOutputReset p) = base + BitVec.ofNat 64 (2*p.outputStride) := by
    simpa only [neonOutputReset, Nat.mul_comm 4 (p.rows/2*2)]
      using pointer_reset base (p.rows/2*2*4) (2*p.outputStride)
  have hi : s.locals "i0" = some (.pointer (p.input + BitVec.ofNat 64 (p.rows/2*2*p.inputStride))) := hl.input0
  have ho : s.locals "o0" = some (.pointer (p.output + BitVec.ofNat 64 (4*(p.rows/2*2)))) := hl.output0
  have ho1 : s.locals "o1" = some (.pointer
      (neonColumn1 (neonActiveStrip p width) + BitVec.ofNat 64 (4*(p.rows/2*2)))) := by
    have he : neonColumn1 ((neonActiveStrip p width).rowSlice (p.rows/2*2) (p.rows%2)) =
        neonColumn1 (neonActiveStrip p width) + BitVec.ofNat 64 (4*(p.rows/2*2)) := by
      unfold neonColumn1
      by_cases small : width < 2 <;>
        simp only [MatrixCopy.rowSlice, neonActiveStrip, small, ↓reduceIte, Nat.reduceEqDiff] <;> ac_rfl
    exact he ▸ hl.output1
  have sub : max ((width : Int)-2) 0 = (width-2 : Nat) := by omega
  let t0 := update s "i0" (.pointer (p.input + 8#64))
  let t1 := update t0 "i1" (.pointer ((p.input + 8#64) + BitVec.ofNat 64 p.inputStride))
  let t2 := update t1 "o0" (.pointer (p.output + BitVec.ofNat 64 (2*p.outputStride)))
  let t3 := update t2 "o1" (.pointer (neonColumn1 (neonActiveStrip p width) + BitVec.ofNat 64 (2*p.outputStride)))
  have e0 := eval_pointer_add cfg s "i0" "input_reset" _ _ hi h.inputReset
  rw [ir] at e0
  have e1 := eval_pointer_add cfg t0 "i0" "input_stride" (p.input + 8#64) p.inputStride
    (by simp [t0, update]) (by simpa [t0, update] using h.inputStride)
  simp only [BitVec.ofInt_natCast] at e1
  have e2 := eval_pointer_add cfg t1 "o0" "output_reset" _ _
    (by simpa [t1, t0, update] using ho) (by simpa [t1, t0, update] using h.outputReset)
  rw [outr] at e2
  have e3 := eval_pointer_add cfg t2 "o1" "output_reset" _ _
    (by simpa [t2, t1, t0, update] using ho1) (by simpa [t2, t1, t0, update] using h.outputReset)
  rw [outr] at e3
  have e4 : eval cfg t3 (.call .differenceOrZero [(.var "block_width"), (.var "tile_width")]) =
      some (.integer (width-2 : Nat)) := by
    simp [eval, intrinsic, t3, t2, t1, t0, update, hw, h.tileWidth, sub]
  exact .seq (.assign e0) (.seq (.assign e1) (.seq (.assign e2) (.seq (.assign e3)
    (.seq (.assign e4) .skip))))

@[simp] theorem neon_column_after_memory (s : State) (p : MatrixCopy) (width : Nat) :
    (neonColumnAfter s p width).memory = s.memory := rfl

theorem neon_column_after_width (s : State) (p : MatrixCopy) (width : Nat) :
    (neonColumnAfter s p width).locals "block_width" = some (.integer (width-2 : Nat)) := by
  simp [neonColumnAfter, update]



theorem neon_column_prepared_constants (s : State) (p : MatrixCopy) (width : Nat)
    (h : NeonConstants s p) : NeonConstants (neonColumnPrepared s p width) p := by
  by_cases small : width < 2 <;> constructor <;>
    simp [neonColumnPrepared, update, small, h.height, h.inputStride, h.outputStride,
      h.tileWidth, h.hbytes, h.offset, h.inputReset, h.outputReset]

@[simp] theorem neon_column_prepared_memory (s : State) (p : MatrixCopy) (width : Nat) :
    (neonColumnPrepared s p width).memory = s.memory := by
  unfold neonColumnPrepared
  split <;> rfl

theorem neon_column_after_locals (s : State) (p : MatrixCopy) (width : Nat)
    (h : NeonConstants s p) (large : 2 ≤ width) :
    NeonColumnLocals (neonColumnAfter s p width) (p.slice 2 (p.cols-2)) (width-2) := by
  constructor
  · constructor <;> simp [neonColumnAfter, update, MatrixCopy.slice, neonInputOffset,
      neonInputReset, neonOutputReset, h.height, h.inputStride, h.outputStride,
      h.tileWidth, h.hbytes, h.offset, h.inputReset, h.outputReset,
      neonInputOffset, neonInputReset, neonOutputReset] at *
  · exact neon_column_after_width s p width
  · simp [neonColumnAfter, update, MatrixCopy.slice]
  · simp [neonColumnAfter, update, MatrixCopy.slice]
  · simp [neonColumnAfter, update, MatrixCopy.slice]
  · simp only [neonColumnAfter, update, MatrixCopy.slice, neonColumn1, neonActiveStrip,
      show ¬ width < 2 by omega, ↓reduceIte, Nat.reduceEqDiff]
    congr 2
    ac_rfl

/-- One exact source outer-loop body, including all row iterations, the odd
row tail, modular pointer resets, and saturating width subtraction. -/
theorem neon_column_body_total (cfg : Config) (s : State) (p : MatrixCopy) (width : Nat)
    (h : NeonColumnLocals s p width) (bound : p.rows < 2^64)
    (safe : NeonStripSafe s.memory (neonActiveStrip p width))
    (sep : (neonActiveStrip p width).separated) :
    ∃ t, Exec cfg neonOuterBody s t ∧ t.memory = (neonActiveStrip p width).result s.memory ∧
      t.locals "block_width" = some (.integer (width-2 : Nat)) ∧
      (2 ≤ width → NeonColumnLocals t (p.slice 2 (p.cols-2)) (width-2)) := by
  let prep := neonColumnPrepared s p width
  have hp := neon_column_prepared_locals s p width h
  have hc := neon_column_prepared_constants s p width h.toNeonConstants
  have hw : prep.locals "block_width" = some (.integer width) := by
    by_cases small : width < 2 <;> simp [prep, neonColumnPrepared, update, small, h.width]
  have activeWidth : (neonActiveStrip p width).cols = 1 ∨ (neonActiveStrip p width).cols = 2 := by
    unfold neonActiveStrip
    split <;> simp
  obtain ⟨u, hu, hm, hl⟩ := neon_strip_total cfg prep (neonActiveStrip p width) hp activeWidth
    bound (by simpa only [prep, neon_column_prepared_memory] using safe) sep
  have uc := hc.frame hu
  have uw : u.locals "block_width" = some (.integer width) :=
    (hu.locals_frame "block_width" (by decide)).trans hw
  refine ⟨neonColumnAfter u p width, ?_, ?_, neon_column_after_width u p width,
    fun large => neon_column_after_locals u p width uc large⟩
  · apply exec_take_drop 2 (neon_column_prep_exec cfg s p width h)
    cases hu with
    | seq rows tail =>
      exact .seq rows (.seq tail (neon_column_post_exec cfg u p width uc uw hl))
  · simpa only [neon_column_after_memory, prep, neon_column_prepared_memory] using hm

end Salty.Kernels.X32Transpose
