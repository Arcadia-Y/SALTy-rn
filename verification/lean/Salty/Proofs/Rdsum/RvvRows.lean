import Salty.Proofs.Rdsum.RvvBatchCorrect

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def rvvRowLoop (kind : Interpretation) : Stmt := firstStatement (dropStatements 10 (rvvChannels kind))

theorem rvv_row_loop_shape (kind : Interpretation) : rvvRowLoop kind =
    .loop (.bin .gt (.var "r") (.lit 0)) (rvvBatches kind) := by cases kind <;> rfl

theorem batch_pointers_next (kind : Interpretation) (m : Memory) (input zero : Address)
    (width stride first remaining : Nat) (pointers : Nat → Address)
    (ptrs : ∀ (i : Nat), i < 7 → i < remaining →
      pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∀ i, i < 7 → i < remaining-batchSize remaining →
      (groupFold kind m zero width (7*stride) ((batchSize remaining+6)/7)
        pointers (batchSize remaining) ((List.range width).map (fun _ => 0))).pointers i =
        input+BitVec.ofNat 64 ((first+batchSize remaining+i)*stride) := by
  intro i hi live
  have large : 252 < remaining := by unfold batchSize at live; omega
  have bs : batchSize remaining = 252 := Nat.min_eq_right (by omega)
  rw [bs]
  change (groupFold kind m zero width (7*stride) 36 pointers 252 _).pointers i = _
  rw [groupFold_full_pointers kind m zero width (7*stride) 36 pointers 252 _ (by decide) i hi,
    ptrs i hi (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  simp only [Nat.add_mul]
  omega

/-- Every iteration is the extracted bounded batch; strong induction on the
remaining rows establishes termination and the original-memory column sum. -/
theorem rvv_rows_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero : Address) (width stride total first remaining : Nat) (pointers : Nat → Address)
    (initial : Nat → BitVec 32) (bound : remaining < 2^31) (within : first+remaining ≤ total)
    (cap : width ≤ cfg.capacity) (loc : BatchLocals kind s pointers zero remaining width stride initial)
    (readable : ∀ row, row < total → ∀ a,
      Footprint (input+BitVec.ofNat 64 (row*stride)) width a → s.memory.readable a = true)
    (zeroRead : ∀ a, Footprint zero width a → s.memory.readable a = true)
    (zeros : ∀ column, column < width → s.memory.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < remaining →
      pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∃ t, Exec cfg (rvvRowLoop kind) s t ∧ t.memory = s.memory ∧
      t.locals (accumulatorName kind) = some (.words32 ((List.range width).map
        (fun column => initial column+intervalSum kind s.memory input stride first remaining column))) := by
  induction remaining using Nat.strongRecOn generalizing s first pointers initial with
  | ind remaining ih =>
    by_cases empty : remaining = 0
    · subst remaining
      refine ⟨s,?_,rfl,?_⟩
      · rw [rvv_row_loop_shape]
        apply Exec.done (v := .integer 0)
        · simp [eval, binary, loc.remaining]
        · rfl
      · simpa [intervalSum, widen32, sumWords] using loc.acc
    · have positive : 0 < remaining := by omega
      have bsle : batchSize remaining ≤ remaining := Nat.min_le_left ..
      have bspos : 0 < batchSize remaining := by unfold batchSize; omega
      have safe : GroupsSafe s.memory zero width (7*stride) ((batchSize remaining+6)/7)
          pointers (batchSize remaining) := by
        apply groups_safe_of_rows s.memory input zero stride width total _ readable zeroRead first
          (batchSize remaining) pointers (group_count_ceiling _) (by omega)
        intro i hi live
        exact ptrs i hi (by omega)
      obtain ⟨u,batch,mem,uloc⟩ := rvv_batch_correct kind cfg s input zero width stride first remaining
        pointers initial positive bound cap loc safe zeros (fun i hi live => ptrs i hi (by omega))
      obtain ⟨t,rest,tmem,acc⟩ := ih (remaining-batchSize remaining) (by omega) u
        (first+batchSize remaining) _ _ (by omega) (by omega) uloc
        (by simpa only [mem] using readable) (by simpa only [mem] using zeroRead)
        (by simpa only [mem] using zeros) (batch_pointers_next kind s.memory input zero width stride first remaining pointers ptrs)
      refine ⟨t,?_,tmem.trans mem,?_⟩
      · rw [rvv_row_loop_shape]
        apply Exec.more (v := .integer 1) (t := u)
        · simp [eval, binary, loc.remaining, empty, show (0 : Int) < remaining by omega]
        · rfl
        · exact batch
        · simpa only [← rvv_row_loop_shape] using rest
      · rw [mem] at acc
        have splitSum : ∀ column, intervalSum kind s.memory input stride first remaining column =
            intervalSum kind s.memory input stride first (batchSize remaining) column +
            intervalSum kind s.memory input stride (first+batchSize remaining) (remaining-batchSize remaining) column := by
          intro column
          have h := intervalSum_add kind s.memory input stride first (batchSize remaining) (remaining-batchSize remaining) column
          simpa only [Nat.add_sub_of_le bsle] using h
        simpa only [splitSum, BitVec.add_assoc] using acc

end Salty.Kernels.Rdsum
