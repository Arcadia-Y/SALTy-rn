import Salty.Proofs.X32Transpose.Execution
import Salty.Proofs.Core.MatrixPlan

namespace Salty.Kernels.X32Transpose
open CByte

private theorem rowsWrite_range (p : MatrixCopy) (original working : Memory) (start count : Nat) :
    rowsWrite original working (p.input + BitVec.ofNat 64 (start * p.inputStride))
      (p.output + BitVec.ofNat 64 (4 * start)) p.inputStride p.outputStride p.cols count =
      (List.range' start count).foldl (p.writeRow original) working := by
  induction count generalizing working start with
  | zero => simp [rowsWrite]
  | succ count ih =>
    rw [rowsWrite, p.strided_writeRow]
    have hi : p.input + BitVec.ofNat 64 (start * p.inputStride) + BitVec.ofNat 64 p.inputStride =
        p.input + BitVec.ofNat 64 ((start + 1) * p.inputStride) := by
      simp [Nat.add_mul, BitVec.ofNat_add, BitVec.add_assoc]
    have ho : p.output + BitVec.ofNat 64 (4 * start) + 4#64 =
        p.output + BitVec.ofNat 64 (4 * (start + 1)) := by
      simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
    rw [hi, ho, ih]
    simp only [List.range'_succ, List.foldl_cons]

theorem rowsWrite_matrix (p : MatrixCopy) (original : Memory) :
    rowsWrite original original p.input p.output p.inputStride p.outputStride p.cols p.rows =
      p.result original := by
  have h := rowsWrite_range p original original 0 p.rows
  simp only [Nat.zero_mul, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    ← List.range_eq_range'] at h
  exact h.trans (p.rows_fold original original)

/-- A complete execution of the extracted RVV row loop refines the common
transpose memory result for its current active column strip. The enclosing
column loop and function initialization are separate remaining obligations. -/
theorem rvv_rows_matrix (cfg : Config) (s : State) (p : MatrixCopy)
    (locals : RowLocals s p.rows p.cols p.input p.output p.inputStride p.outputStride)
    (bound : p.rows < 2^64) (capacity : p.cols ≤ cfg.capacity)
    (safe : RowsSafe s.memory p.input p.output p.inputStride p.outputStride p.rows p.cols) :
    ∃ t, Exec cfg rvvRows s t ∧ t.memory = p.result s.memory := by
  obtain ⟨t, ht, hm⟩ := rvv_rows_original cfg s p.rows p.cols p.input p.output
    p.inputStride p.outputStride locals bound capacity safe
  exact ⟨t, ht, hm.trans (rowsWrite_matrix p s.memory)⟩

end Salty.Kernels.X32Transpose
