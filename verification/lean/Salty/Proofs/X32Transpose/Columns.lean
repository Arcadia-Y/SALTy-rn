import Salty.Proofs.X32Transpose.Matrix
import Salty.Proofs.X32Transpose.Safety

namespace Salty.Kernels.X32Transpose
open CByte

def rvvColumnBody : Stmt := loopBody rvvColumns
def columnPrep : Stmt := takeStatements 4 rvvColumnBody
def columnPost : Stmt := dropStatements 5 rvvColumnBody

structure ColumnLocals (s : State) (p : MatrixCopy) : Prop where
  width : s.locals "bw" = some (.integer p.cols)
  inputPtr : s.locals "input" = some (.pointer p.input)
  outputPtr : s.locals "output" = some (.pointer p.output)
  height : s.locals "block_height" = some (.integer p.rows)
  inputStride : s.locals "input_stride" = some (.integer p.inputStride)
  outputStride : s.locals "output_stride" = some (.integer p.outputStride)

def columnPrepared (s : State) (p : MatrixCopy) (vl : Nat) : State :=
  let t := update s "vl" (.integer vl)
  let t := update t "i" (.pointer p.input)
  let t := update t "o" (.pointer p.output)
  update t "bh" (.integer p.rows)

def remainingColumns (p : MatrixCopy) (vl : Nat) : MatrixCopy :=
  {p with input := p.input + BitVec.ofNat 64 (4 * vl),
          output := p.output + BitVec.ofNat 64 (vl * p.outputStride),
          cols := p.cols - vl}

def columnAfter (s : State) (p : MatrixCopy) (vl : Nat) : State :=
  let t := update s "input" (.pointer (remainingColumns p vl).input)
  let t := update t "output" (.pointer (remainingColumns p vl).output)
  update t "bw" (.integer (p.cols - vl : Nat))

theorem column_prep_exec (cfg : Config) (s : State) (p : MatrixCopy) (h : ColumnLocals s p) :
    Exec cfg columnPrep s (columnPrepared s p (cfg.choose p.cols)) := by
  apply run_sound (fuel := 12)
  simp [columnPrep, rvvColumnBody, rvvColumns, takeStatements, firstStatement,
    dropStatements, loopBody, Generated.X32Transpose.rvv, run, eval, intrinsic,
    h.width, h.height, h.inputPtr, h.outputPtr, update, columnPrepared]

theorem column_prepared_locals (s : State) (p : MatrixCopy) (vl : Nat) (h : ColumnLocals s p) :
    ColumnLocals (columnPrepared s p vl) p ∧
    RowLocals (columnPrepared s p vl) p.rows vl p.input p.output p.inputStride p.outputStride := by
  constructor <;> constructor <;>
    simp [columnPrepared, update, h.width, h.height, h.inputPtr, h.outputPtr,
      h.inputStride, h.outputStride]

theorem column_locals_frame (cfg : Config) (s t : State) (p : MatrixCopy)
    (h : ColumnLocals s p) (he : Exec cfg rvvRows s t) : ColumnLocals t p := by
  constructor
  · exact (he.locals_frame "bw" (by decide)).trans h.width
  · exact (he.locals_frame "input" (by decide)).trans h.inputPtr
  · exact (he.locals_frame "output" (by decide)).trans h.outputPtr
  · exact (he.locals_frame "block_height" (by decide)).trans h.height
  · exact (he.locals_frame "input_stride" (by decide)).trans h.inputStride
  · exact (he.locals_frame "output_stride" (by decide)).trans h.outputStride

theorem column_post_exec (cfg : Config) (s : State) (p : MatrixCopy) (vl : Nat)
    (h : ColumnLocals s p) (hvl : s.locals "vl" = some (.integer vl))
    (bounded : vl ≤ p.cols) (size : p.cols < 2^64) :
    Exec cfg columnPost s (columnAfter s p vl) := by
  have hc := cast_sub p.cols vl bounded size
  have hi : BitVec.ofInt 64 (4 * (vl : Int)) = BitVec.ofNat 64 (4 * vl) := by
    change BitVec.ofInt 64 ((4 : Nat) * (vl : Int)) = _
    rw [← Int.natCast_mul, BitVec.ofInt_natCast]
  have hp : BitVec.ofInt 64 ((p.output.toNat : Int) + convert .u64 (vl * p.outputStride : Nat)) =
      p.output + BitVec.ofNat 64 (vl * p.outputStride) := by
    rw [BitVec.ofInt_add, cast_u64_word]
    simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply run_sound (fuel := 12)
  simp [columnPost, rvvColumnBody, rvvColumns, firstStatement, dropStatements, loopBody,
    Generated.X32Transpose.rvv, run, eval, binary, update,
    h.width, h.inputPtr, h.outputPtr, h.outputStride, hvl,
    pointer_integer_add, cast_u64_word, columnAfter, remainingColumns, hc, ← Int.natCast_mul,
    hp, hi, BitVec.ofInt_natCast]

theorem column_after_locals (s : State) (p : MatrixCopy) (vl : Nat) (h : ColumnLocals s p) :
    ColumnLocals (columnAfter s p vl) (remainingColumns p vl) := by
  constructor <;> simp [columnAfter, remainingColumns, update, h.height, h.inputStride, h.outputStride]

/-- Execute one exact extracted outer-loop body, including initialization of
row locals, all row iterations, pointer arithmetic, and width subtraction. -/
theorem rvv_column_exec (cfg : Config) (s : State) (p : MatrixCopy)
    (h : ColumnLocals s p) (rowsBound : p.rows < 2^64) (colsBound : p.cols < 2^64)
    (safe : RowsSafe s.memory p.input p.output p.inputStride p.outputStride p.rows (cfg.choose p.cols)) :
    ∃ t, Exec cfg rvvColumnBody s t ∧
      t.memory = ({p with cols := cfg.choose p.cols} : MatrixCopy).result s.memory ∧
      ColumnLocals t (remainingColumns p (cfg.choose p.cols)) := by
  let vl := cfg.choose p.cols
  let prep := columnPrepared s p vl
  have hp := column_prepared_locals s p vl h
  have cap : vl ≤ cfg.capacity := Nat.le_trans (cfg.bounded p.cols) (Nat.min_le_right ..)
  have len : vl ≤ p.cols := Nat.le_trans (cfg.bounded p.cols) (Nat.min_le_left ..)
  obtain ⟨u, hu, hm⟩ := rvv_rows_matrix cfg prep {p with cols := vl} hp.2 rowsBound cap safe
  have hc := column_locals_frame cfg prep u p hp.1 hu
  have hv : u.locals "vl" = some (.integer vl) := by
    rw [hu.locals_frame "vl" (by decide)]
    simp [prep, columnPrepared, update]
  refine ⟨columnAfter u p vl, ?_, hm, column_after_locals u p vl hc⟩
  exact exec_take_drop 4 (column_prep_exec cfg s p h)
    (.seq hu (column_post_exec cfg u p vl hc hv len colsBound))

/-- Total correctness of the exact RVV outer loop, with no bound on the
number of row or column iterations. Every legal progressing VL choice yields
the same full-memory matrix result. -/
theorem rvv_columns_total (cfg : Config) (s : State) (p : MatrixCopy)
    (locals : ColumnLocals s p) (rowsBound : p.rows < 2^64) (colsBound : p.cols < 2^64)
    (safe : RowsSafe s.memory p.input p.output p.inputStride p.outputStride p.rows p.cols)
    (sep : p.separated) :
    ∃ t, Exec cfg rvvColumns s t ∧ t.memory = p.result s.memory := by
  by_cases zero : p.cols = 0
  · refine ⟨s, ?_, ?_⟩
    · apply Exec.done (v := .integer 0)
      · simp [rvvColumns, firstStatement, dropStatements, Generated.X32Transpose.rvv,
          eval, binary, convert, locals.width, zero]
      · rfl
    · rw [p.result_columnFold s.memory sep, zero]
      rfl
  · let vl := cfg.choose p.cols
    have pos : 0 < vl := cfg.positive p.cols (by omega)
    have len : vl ≤ p.cols := Nat.le_trans (cfg.bounded p.cols) (Nat.min_le_left ..)
    have preEq : p.slice 0 vl = {p with cols := vl} := by simp [MatrixCopy.slice]
    have suffix : p.slice vl (p.cols-vl) = remainingColumns p vl := rfl
    have stripSafe := safe.slice 0 vl (by omega)
    simp only [MatrixCopy.slice, Nat.mul_zero, Nat.zero_mul, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] at stripSafe
    obtain ⟨u, hu, hm, hl⟩ := rvv_column_exec cfg s p locals rowsBound colsBound stripSafe
    have nextSafe := (safe.slice vl (p.cols-vl) (by omega)).permissions
      (other := u.memory) (by rw [hm]; exact MatrixCopy.result_readable ..)
      (by rw [hm]; exact MatrixCopy.result_writable ..)
    obtain ⟨t, ht, hmem⟩ := rvv_columns_total cfg u (remainingColumns p vl) hl rowsBound
      (by simp only [remainingColumns]; omega) nextSafe
      (p.slice_separated vl (p.cols-vl) (by omega) sep)
    refine ⟨t, ?_, ?_⟩
    · apply Exec.more (v := .integer 1) (t := u)
      · simp [rvvColumns, firstStatement, dropStatements, Generated.X32Transpose.rvv,
          eval, binary, convert, locals.width, zero, show (0 : Int) < p.cols by omega]
      · rfl
      · exact hu
      · exact ht
    · rw [hmem, hm]
      rw [← suffix, ← preEq]
      exact safe.prefix_remaining_result vl len sep
termination_by p.cols
decreasing_by simp only [remainingColumns]; omega

end Salty.Kernels.X32Transpose
