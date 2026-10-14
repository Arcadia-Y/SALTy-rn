import Salty.Proofs.Rdsum.NeonMainRows

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def mainReadSpan : Interpretation → Nat
  | .signed => 16
  | .unsigned => 40

structure NeonMainLocals (kind : Interpretation) (s : State) (pointers : Nat → Address) (zero : Address)
    (remaining : Int) (increment : Nat) (acc : Nat → List (BitVec 16)) : Prop where
  rows : ∀ i, i < 7 → s.locals (rowName i) = some (.pointer (pointers i))
  zero : s.locals "zero" = some (.pointer zero)
  remaining : s.locals "current_batch" = some (.integer remaining)
  increment : s.locals "input_increment" = some (.integer increment)
  acc : ∀ j, j < neonChunks kind true → s.locals (neonHalfName kind true j) = some (.halfwords (acc j))

def mainDecls : Interpretation → Stmt
  | .signed => .seq .skip (.seq .skip .skip)
  | .unsigned => .seq .skip (.seq .skip (.seq .skip (.seq .skip .skip)))

theorem main_group_data_shape (kind : Interpretation) : dropStatements 6 (neonGroup kind true) =
    appendStatements (mainDecls kind) (appendStatements (mainRowsCode kind 7) (neonPointersCode true)) := by
  cases kind <;> rfl

theorem main_chunk_footprint (kind : Interpretation) (ptr a : Address) (chunk : Nat)
    (within : chunk < neonChunks kind true)
    (h : Footprint (ptr+BitVec.ofNat 64 (8*chunk)) (mainLoadWidth kind) a) :
    Footprint ptr (mainReadSpan kind) a := by
  apply footprint_shift_within (start := 8*chunk) ?_ h
  cases kind <;> simp [neonChunks, neonWidth] at within <;> simp [mainLoadWidth, mainReadSpan] <;> omega

/-- Complete main-path group, including zero substitution, all seven rows,
source load widths, and the seven pointer advances. -/
theorem neon_main_group_exec (kind : Interpretation) (cfg : Config) (s : State)
    (pointers : Nat → Address) (zero : Address) (remaining : Int) (increment : Nat)
    (acc : Nat → List (BitVec 16)) (ha : ∀ j, j < neonChunks kind true → (acc j).length = 8)
    (loc : NeonMainLocals kind s pointers zero remaining increment acc)
    (safe : ∀ i, i < 7 → ∀ a,
      Footprint (selectedPointers pointers remaining zero i) (mainReadSpan kind) a → s.memory.readable a = true) :
    ∃ t, Exec cfg (neonGroup kind true) s t ∧ t.memory = s.memory ∧
      NeonMainLocals kind t (groupPointers pointers zero remaining increment) zero remaining increment
        (mainRowsAcc kind s.memory (selectedPointers pointers remaining zero) acc 7) := by
  let u := neonZerosAfter true s remaining zero
  have zeros : Exec cfg (neonZeroBranches true) s u := neon_zeros_exec cfg s true remaining zero loc.remaining loc.zero
  have umem : u.memory = s.memory := neonZerosAfter_memory true s remaining zero
  have ptrs : ∀ i, i < 7 → u.locals (rowName i) = some (.pointer (selectedPointers pointers remaining zero i)) := by
    intro i hi
    have h := neonZerosAfter_row true s remaining zero i hi
    simp only [neonRowName, ↓reduceIte] at h
    rw [h]
    by_cases absent : 0 < i ∧ remaining ≤ (i : Int) <;> simp [selectedPointers, absent, loc.rows i hi]
  have accum : ∀ j, j < neonChunks kind true → u.locals (neonHalfName kind true j) = some (.halfwords (acc j)) := by
    intro j hj
    apply Eq.trans (zeros.locals_frame _ ?_) (loc.acc j hj)
    cases kind with
    | signed =>
      have cases : j = 0 ∨ j = 1 := by simp [neonChunks, neonWidth] at hj; omega
      rcases cases with rfl | rfl <;> rfl
    | unsigned =>
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [neonChunks, neonWidth] at hj; omega
      rcases cases with rfl | rfl | rfl | rfl <;> rfl
  let v := mainRowsAfter kind u (selectedPointers pointers remaining zero) acc 7
  have rows : Exec cfg (mainRowsCode kind 7) u v := main_rows_exec kind cfg u _ acc 7 (by decide) ptrs ha accum
    (fun i hi j hj a h => by rw [umem]; exact safe i hi a (main_chunk_footprint kind _ a j hj h))
  let t := neonPointersAfter true v (selectedPointers pointers remaining zero) increment
  have ptrstep : Exec cfg (neonPointersCode true) v t := neon_pointers_exec cfg v true _ increment
    (by intro i hi; simpa only [neonRowName, ↓reduceIte, v, mainRowsAfter_row kind u _ acc 7 i hi] using ptrs i hi)
    ((rows.locals_frame _ (by cases kind <;> rfl)).trans ((zeros.locals_frame _ (by rfl)).trans loc.increment))
  have body : Exec cfg (neonGroup kind true) s t := by
    apply exec_take_drop (t := u) 6
    · rw [neon_zero_shape]; exact zeros
    · rw [main_group_data_shape]
      apply appendStatements_exec (t := u)
      · cases kind <;> apply run_sound (fuel := 6) <;> rfl
      · exact appendStatements_exec rows ptrstep
  refine ⟨t,body,?_,?_⟩
  · change v.memory = s.memory
    rw [mainRowsAfter_memory, umem]
  · constructor
    · intro i hi
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [t, neonPointersAfter, neonRowName, rowName, update, groupPointers]
    · exact (body.locals_frame _ (by cases kind <;> rfl)).trans loc.zero
    · exact (body.locals_frame _ (by cases kind <;> rfl)).trans loc.remaining
    · exact (body.locals_frame _ (by cases kind <;> rfl)).trans loc.increment
    · intro j hj
      have unchanged : t.locals (neonHalfName kind true j) = v.locals (neonHalfName kind true j) := by
        apply ptrstep.locals_frame
        cases kind with
        | signed =>
          have cases : j = 0 ∨ j = 1 := by simp [neonChunks, neonWidth] at hj; omega
          rcases cases with rfl | rfl <;> rfl
        | unsigned =>
          have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [neonChunks, neonWidth] at hj; omega
          rcases cases with rfl | rfl | rfl | rfl <;> rfl
      rw [unchanged, mainRowsAfter_acc kind u _ acc 7 j hj (accum j hj), umem]

end Salty.Kernels.Rdsum
