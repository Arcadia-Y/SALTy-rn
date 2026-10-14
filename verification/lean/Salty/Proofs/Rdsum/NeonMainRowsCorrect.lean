import Salty.Proofs.Rdsum.NeonMainBatch

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

theorem mainFold_pointers (kind : Interpretation) (m : Memory) (zero : Address) (increment count : Nat)
    (pointers : Nat → Address) (remaining : Int) :
    (groupFold kind m zero 8 increment count pointers remaining ((List.range 8).map (fun _ => 0))).pointers =
      (mainFold kind m zero increment count pointers remaining zeroMainAcc).pointers := by
  have h := congrArg GroupResult.pointers (mainFold_chunk kind m zero increment count pointers remaining zeroMainAcc 0)
  simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, zeroMainAcc] using h

theorem main_batch_pointers_next (kind : Interpretation) (m : Memory) (input zero : Address)
    (stride first remaining : Nat) (pointers : Nat → Address)
    (ptrs : ∀ (i : Nat), i < 7 → i < remaining → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∀ (i : Nat), i < 7 → i < remaining-batchSize remaining →
      (mainFold kind m zero (7*stride) ((batchSize remaining+6)/7) pointers (batchSize remaining) zeroMainAcc).pointers i =
        input+BitVec.ofNat 64 ((first+batchSize remaining+i)*stride) := by
  rw [← mainFold_pointers]
  exact batch_pointers_next kind m input zero 8 stride first remaining pointers ptrs

theorem neon_main_row_shape (kind : Interpretation) : neonRowLoop kind true =
    .loop (.bin .gt (.var "r") (.lit 0)) (neonBatch kind true) := by cases kind <;> rfl

/-- All main-path row batches terminate, retaining the source's padded load
footprint while accumulating exactly the original row interval. -/
theorem neon_main_rows_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero : Address) (stride total first remaining : Nat) (pointers : Nat → Address)
    (initial : Nat → BitVec 32) (bound : remaining < 2^31) (within : first+remaining ≤ total)
    (loc : NeonMainBatchLocals kind s pointers zero remaining stride initial)
    (readable : ∀ row, row < total → ∀ a,
      Footprint (input+BitVec.ofNat 64 (row*stride)) (mainReadSpan kind) a → s.memory.readable a = true)
    (zeroRead : ∀ a, Footprint zero (mainReadSpan kind) a → s.memory.readable a = true)
    (zeros : ∀ column, column < neonWidth kind true → s.memory.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < remaining → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∃ t, Exec cfg (neonRowLoop kind true) s t ∧ t.memory = s.memory ∧
      (∀ word, word < neonWidth kind true/4 → t.locals (neonWordName true word) =
        some (.words32 (wordValues (fun column => initial column+intervalSum kind s.memory input stride first remaining column) word))) := by
  induction remaining using Nat.strongRecOn generalizing s first pointers initial with
  | ind remaining ih =>
    by_cases empty : remaining = 0
    · subst remaining
      refine ⟨s,?_,rfl,?_⟩
      · rw [neon_main_row_shape]
        apply Exec.done (v := .integer 0)
        · simp [eval, binary, loc.remaining]
        · rfl
      · intro word hw
        simpa [wordValues, intervalSum, widen32, sumWords] using loc.words word hw
    · have positive : 0 < remaining := by omega
      have bsle : batchSize remaining ≤ remaining := Nat.min_le_left ..
      have bspos : 0 < batchSize remaining := by unfold batchSize; omega
      have safe : GroupsSafe s.memory zero (mainReadSpan kind) (7*stride) ((batchSize remaining+6)/7)
          pointers (batchSize remaining) := by
        apply groups_safe_of_rows s.memory input zero stride (mainReadSpan kind) total _ readable zeroRead first
          (batchSize remaining) pointers (group_count_ceiling _) (by omega)
        intro i hi live
        exact ptrs i hi (by omega)
      obtain ⟨u,batch,mem,uloc⟩ := neon_main_batch_correct kind cfg s input zero stride first remaining pointers initial positive bound loc safe zeros
        (fun i hi live => ptrs i hi (by omega))
      obtain ⟨t,rest,tmem,words⟩ := ih (remaining-batchSize remaining) (by omega) u (first+batchSize remaining) _ _
        (by omega) (by omega) uloc (by simpa only [mem] using readable)
        (by simpa only [mem] using zeroRead) (by simpa only [mem] using zeros)
        (main_batch_pointers_next kind s.memory input zero stride first remaining pointers ptrs)
      refine ⟨t,?_,tmem.trans mem,?_⟩
      · rw [neon_main_row_shape]
        apply Exec.more (v := .integer 1) (t := u)
        · simp [eval, binary, loc.remaining, show (0 : Int) < remaining by omega, empty]
        · rfl
        · exact batch
        · simpa only [← neon_main_row_shape] using rest
      · intro word hw
        have h := words word hw
        rw [mem] at h
        have splitSum : ∀ column, intervalSum kind s.memory input stride first remaining column =
            intervalSum kind s.memory input stride first (batchSize remaining) column +
            intervalSum kind s.memory input stride (first+batchSize remaining) (remaining-batchSize remaining) column := by
          intro column
          have h := intervalSum_add kind s.memory input stride first (batchSize remaining) (remaining-batchSize remaining) column
          simpa only [Nat.add_sub_of_le bsle] using h
        simpa only [splitSum, BitVec.add_assoc] using h

end Salty.Kernels.Rdsum
