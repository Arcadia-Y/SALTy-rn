import Salty.Spec.X32Transpose
import Salty.Proofs.X32Transpose.NeonInit

namespace Salty.Kernels.X32Transpose
open CByte

theorem empty_rows_result (m : Memory) (p : MatrixCopy) (empty : p.rows = 0) : p.result m = m := by
  rw [p.result_rowFold, empty]
  rfl

theorem source_effective_result (m : Memory) (p : MatrixCopy) :
    (sourceMatrix p).result m = (effectiveMatrix p).result m := by
  by_cases empty : p.rows = 0
  · rw [empty_rows_result m (sourceMatrix p) empty, empty_rows_result m (effectiveMatrix p) empty]
  · simp only [sourceMatrix, effectiveMatrix, empty, ↓reduceIte]

/-- The complete independently extracted source function, including the
mandatory first do-body and the zero-width first-column copy. -/
theorem neon_function_total (cfg : Config) (s : State) (p : MatrixCopy)
    (h : Arguments s p) (heightBound : p.rows < 2^64)
    (outStride : p.cols = 1 ∨ convert .u64 ((p.rows : Int)*4) ≤ p.outputStride)
    (inStride : p.rows = 1 ∨ convert .u64 ((p.cols : Int)*4) ≤ p.inputStride)
    (safe : TransposeSafe s.memory (sourceMatrix p)) (sep : (sourceMatrix p).separated) :
    ∃ t, Exec cfg Generated.X32Transpose.neon s t ∧ t.memory = (effectiveMatrix p).result s.memory := by
  have hi := neon_init_exec cfg s p h outStride inStride
  have hl : NeonColumnLocals (neonInitialized s p) (sourceMatrix p) p.cols :=
    (neon_initialized_locals s p h).withCols _
  have hs : TransposeSafe (neonInitialized s p).memory (sourceMatrix p) := safe
  have outer : ∃ t, Exec cfg neonOuter (neonInitialized s p) t ∧ t.memory = (sourceMatrix p).result s.memory := by
    by_cases zero : p.cols = 0
    · exact neon_outer_zero cfg (neonInitialized s p) (sourceMatrix p)
        (by simpa only [zero] using hl) (by simp [sourceMatrix, zero]) heightBound hs sep
    · have same : (sourceMatrix p).cols = p.cols := by simp [sourceMatrix, zero]
      exact neon_outer_positive cfg (neonInitialized s p) (sourceMatrix p)
        (by simpa only [same] using hl) (by rw [same]; omega) heightBound hs sep
  obtain ⟨t, ht, hm⟩ := outer
  refine ⟨t, exec_take_drop 13 hi (.seq ht .skip), ?_⟩
  rw [hm]
  exact source_effective_result s.memory p

end Salty.Kernels.X32Transpose
