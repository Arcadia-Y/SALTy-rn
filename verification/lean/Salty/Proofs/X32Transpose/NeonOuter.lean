import Salty.Proofs.X32Transpose.Regions

namespace Salty.Kernels.X32Transpose
open CByte

def neonColumnLoop : Stmt :=
  .loop (.bin .ne (.var "block_width") (.cast .u64 (.lit 0))) neonOuterBody

theorem neonOuter_shape : neonOuter = .seq neonOuterBody neonColumnLoop := rfl

/-- Every remaining source column, with arbitrary row count and no iteration
bound. The one-column last strip retains its source alias/overwrite behavior. -/
theorem neon_columns_loop_total (cfg : Config) (s : State) (p : MatrixCopy)
    (h : NeonColumnLocals s p p.cols) (bound : p.rows < 2^64)
    (safe : TransposeSafe s.memory p) (sep : p.separated) :
    ∃ t, Exec cfg neonColumnLoop s t ∧ t.memory = p.result s.memory := by
  by_cases zero : p.cols = 0
  · refine ⟨s, ?_, ?_⟩
    · apply Exec.done (v := .integer 0)
      · simp [neonColumnLoop, eval, binary, h.width, zero, show convert .u64 0 = 0 by decide]
      · rfl
    · rw [p.result_columnFold s.memory sep, zero]
      rfl
  · have stripBound : (if p.cols < 2 then 1 else 2) ≤ p.cols := by split <;> omega
    have activeEq : p.slice 0 (if p.cols < 2 then 1 else 2) = neonActiveStrip p p.cols := by
      simp [MatrixCopy.slice, neonActiveStrip]
    have activeSep : (neonActiveStrip p p.cols).separated := by
      rw [← activeEq]
      exact p.slice_separated 0 _ (by omega) sep
    obtain ⟨u, hu, hm, hw, hl⟩ := neon_column_body_total cfg s p p.cols h bound
      (safe.neon_strip p.cols stripBound) activeSep
    by_cases large : 2 ≤ p.cols
    · have activeTwo : neonActiveStrip p p.cols = p.slice 0 2 := by
        simp [neonActiveStrip, MatrixCopy.slice, show ¬ p.cols < 2 by omega]
      have ns := (safe.slice 2 (p.cols-2) (by omega)).permissions
        (other := u.memory) (by rw [hm]; exact MatrixCopy.result_readable ..)
        (by rw [hm]; exact MatrixCopy.result_writable ..)
      obtain ⟨t, ht, hmem⟩ := neon_columns_loop_total cfg u (p.slice 2 (p.cols-2)) (hl large)
        bound ns (p.slice_separated 2 (p.cols-2) (by omega) sep)
      refine ⟨t, ?_, ?_⟩
      · apply Exec.more (v := .integer 1) (t := u)
        · simp [neonColumnLoop, eval, binary, h.width, zero, show convert .u64 0 = 0 by decide]
        · rfl
        · exact hu
        · exact ht
      · rw [hmem, hm, activeTwo]
        exact safe.common.prefix_remaining_result 2 large sep
    · have one : p.cols = 1 := by omega
      have done : Exec cfg neonColumnLoop u u := by
        apply Exec.done (v := .integer 0)
        · simp [neonColumnLoop, eval, binary, hw, one, show convert .u64 0 = 0 by decide]
        · rfl
      refine ⟨u, ?_, ?_⟩
      · apply Exec.more (v := .integer 1) (t := u)
        · simp [neonColumnLoop, eval, binary, h.width, one, show convert .u64 0 = 0 by decide]
        · rfl
        · exact hu
        · exact done
      · have same : neonActiveStrip p p.cols = p := by
          simp only [neonActiveStrip, one, Nat.reduceLT, ↓reduceIte]
          rw [← one]
        rw [same] at hm
        exact hm
termination_by p.cols
decreasing_by change p.cols-2 < p.cols; omega

/-- The source's mandatory first do-body followed by its loop, for positive
width. The zero-width case is handled separately because it still writes. -/
theorem neon_outer_positive (cfg : Config) (s : State) (p : MatrixCopy)
    (h : NeonColumnLocals s p p.cols) (positive : 0 < p.cols) (bound : p.rows < 2^64)
    (safe : TransposeSafe s.memory p) (sep : p.separated) :
    ∃ t, Exec cfg neonOuter s t ∧ t.memory = p.result s.memory := by
  obtain ⟨t, ht, hm⟩ := neon_columns_loop_total cfg s p h bound safe sep
  have cond : eval cfg s (.bin .ne (.var "block_width") (.cast .u64 (.lit 0))) = some (.integer 1) := by
    simp [eval, binary, h.width, show p.cols ≠ 0 by omega, show convert .u64 0 = 0 by decide]
  change Exec cfg (.loop _ neonOuterBody) s t at ht
  cases ht with
  | done he hf => rw [cond] at he; cases he; cases hf
  | more he hf hb hl => exact ⟨t, by rw [neonOuter_shape]; exact .seq hb hl, hm⟩

/-- The width-zero source do-body copies column zero, including its padded
second-word reads. Its remaining-loop condition is then false. -/
theorem neon_outer_zero (cfg : Config) (s : State) (p : MatrixCopy)
    (h : NeonColumnLocals s p 0) (one : p.cols = 1) (bound : p.rows < 2^64)
    (safe : TransposeSafe s.memory p) (sep : p.separated) :
    ∃ t, Exec cfg neonOuter s t ∧ t.memory = p.result s.memory := by
  have same : neonActiveStrip p 0 = p := by
    simp only [neonActiveStrip, Nat.reduceLT, ↓reduceIte]
    rw [← one]
  obtain ⟨t, ht, hm, hw, _⟩ := neon_column_body_total cfg s p 0 h bound
    (safe.neon_strip 0 (by simp [one])) (by simpa only [same] using sep)
  refine ⟨t, ?_, by simpa only [same] using hm⟩
  rw [neonOuter_shape]
  apply Exec.seq ht
  apply Exec.done (v := .integer 0)
  · simp [neonColumnLoop, eval, binary, hw, show convert .u64 0 = 0 by decide]
  · rfl

end Salty.Kernels.X32Transpose
