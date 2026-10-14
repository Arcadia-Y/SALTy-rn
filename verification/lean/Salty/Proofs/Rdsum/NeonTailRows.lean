import Salty.Proofs.Rdsum.NeonTailBatch

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def batchCount (rows : Nat) : Nat := (rows+251)/252

theorem batchCount_next (remaining : Nat) (positive : 0 < remaining) :
    batchCount (remaining-batchSize remaining) = batchCount remaining-1 := by
  unfold batchCount batchSize
  omega

def neonBatchStep : Stmt := .assign "num_batches" (.checkedSigned32 (.bin .sub (.var "num_batches") (.lit 1)))

theorem neon_tail_row_shape (kind : Interpretation) : neonRowLoop kind false =
    .loop (.bin .gt (.var "num_batches") (.lit 0)) (.seq (neonBatch kind false) neonBatchStep) := by cases kind <;> rfl

theorem neon_batch_step_exec (cfg : Config) (s : State) (remaining : Nat)
    (positive : 0 < remaining) (bound : remaining < 2^31)
    (hn : s.locals "num_batches" = some (.integer (batchCount remaining))) :
    Exec cfg neonBatchStep s (update s "num_batches" (.integer (batchCount (remaining-batchSize remaining)))) := by
  have countPos : 0 < batchCount remaining := by unfold batchCount; omega
  have countBound : batchCount remaining < 2^31 := by unfold batchCount; omega
  have sub : (batchCount remaining : Int)-1 = (batchCount (remaining-batchSize remaining) : Nat) := by
    rw [batchCount_next remaining positive]; omega
  have bounds : -(2^31) ≤ (batchCount remaining : Int)-1 ∧ (batchCount remaining : Int)-1 < 2^31 := by omega
  apply Exec.assign
  have h := checked_sub_eval cfg s (.var "num_batches") (.lit 1) (batchCount remaining) 1
    (by simpa only [eval] using hn) (by simp only [eval]) bounds
  rw [sub] at h
  exact h

theorem NeonTailBatchLocals.set_batches {s : State} {pointers : Nat → Address} {zero : Address}
    {remaining stride : Nat} {initial : Nat → BitVec 32}
    (loc : NeonTailBatchLocals s pointers zero remaining stride initial) (count : Nat) :
    NeonTailBatchLocals (update s "num_batches" (.integer count)) pointers zero remaining stride initial := by
  constructor
  · intro i hi
    have hp := loc.rows i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [update, neonRowName] using hp
  · simpa [update] using loc.zero
  · simpa [update] using loc.remaining
  · simpa [update] using loc.increment
  · simpa [update] using loc.low
  · simpa [update] using loc.high

/-- The tail's explicit num_batches loop executes exactly the necessary
252-row batches and returns both four-word halves of the original column sum. -/
theorem neon_tail_rows_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero : Address) (stride total first remaining : Nat) (pointers : Nat → Address)
    (initial : Nat → BitVec 32) (bound : remaining < 2^31) (within : first+remaining ≤ total)
    (loc : NeonTailBatchLocals s pointers zero remaining stride initial)
    (num : s.locals "num_batches" = some (.integer (batchCount remaining)))
    (readable : ∀ row, row < total → ∀ a,
      Footprint (input+BitVec.ofNat 64 (row*stride)) 8 a → s.memory.readable a = true)
    (zeroRead : ∀ a, Footprint zero 8 a → s.memory.readable a = true)
    (zeros : ∀ column, column < 8 → s.memory.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < remaining → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∃ t, Exec cfg (neonRowLoop kind false) s t ∧ t.memory = s.memory ∧
      let values := (List.range 8).map (fun column => initial column+intervalSum kind s.memory input stride first remaining column);
      t.locals "vacc0_2" = some (.words32 (values.take 4)) ∧
      t.locals "vacc1" = some (.words32 (values.drop 4)) := by
  induction remaining using Nat.strongRecOn generalizing s first pointers initial with
  | ind remaining ih =>
    by_cases empty : remaining = 0
    · subst remaining
      refine ⟨s,?_,rfl,?_,?_⟩
      · rw [neon_tail_row_shape]
        apply Exec.done (v := .integer 0)
        · simp [eval, binary, num, batchCount]
        · rfl
      · simpa [intervalSum, widen32, sumWords] using loc.low
      · simpa [intervalSum, widen32, sumWords] using loc.high
    · have positive : 0 < remaining := by omega
      have bsle : batchSize remaining ≤ remaining := Nat.min_le_left ..
      have bspos : 0 < batchSize remaining := by unfold batchSize; omega
      have safe : GroupsSafe s.memory zero 8 (7*stride) ((batchSize remaining+6)/7)
          pointers (batchSize remaining) := by
        apply groups_safe_of_rows s.memory input zero stride 8 total _ readable zeroRead first
          (batchSize remaining) pointers (group_count_ceiling _) (by omega)
        intro i hi live
        exact ptrs i hi (by omega)
      obtain ⟨u,batch,mem,uloc⟩ := neon_tail_batch_correct kind cfg s input zero stride first remaining
        pointers initial positive bound loc safe zeros (fun i hi live => ptrs i hi (by omega))
      have unum : u.locals "num_batches" = some (.integer (batchCount remaining)) :=
        (batch.locals_frame _ (by cases kind <;> rfl)).trans num
      let v := update u "num_batches" (.integer (batchCount (remaining-batchSize remaining)))
      have step : Exec cfg neonBatchStep u v := neon_batch_step_exec cfg u remaining positive bound unum
      have vmem : v.memory = s.memory := mem
      obtain ⟨t,rest,tmem,low,high⟩ := ih (remaining-batchSize remaining) (by omega) v
        (first+batchSize remaining) _ _ (by omega) (by omega) (uloc.set_batches _) (by simp [v,update])
        (by simpa only [vmem] using readable) (by simpa only [vmem] using zeroRead)
        (by simpa only [vmem] using zeros) (batch_pointers_next kind s.memory input zero 8 stride first remaining pointers ptrs)
      refine ⟨t,?_,tmem.trans vmem,?_,?_⟩
      · rw [neon_tail_row_shape]
        apply Exec.more (v := .integer 1) (t := v)
        · have countPositive : (0 : Int) < batchCount remaining := by unfold batchCount; omega
          simp [eval, binary, num, countPositive, show batchCount remaining ≠ 0 by omega]
        · rfl
        · exact .seq batch step
        · simpa only [← neon_tail_row_shape] using rest
      all_goals
        rw [vmem] at low high
        have splitSum : ∀ column, intervalSum kind s.memory input stride first remaining column =
            intervalSum kind s.memory input stride first (batchSize remaining) column +
            intervalSum kind s.memory input stride (first+batchSize remaining) (remaining-batchSize remaining) column := by
          intro column
          have h := intervalSum_add kind s.memory input stride first (batchSize remaining) (remaining-batchSize remaining) column
          simpa only [Nat.add_sub_of_le bsle] using h
        first
        | simpa only [splitSum, BitVec.add_assoc] using low
        | simpa only [splitSum, BitVec.add_assoc] using high

end Salty.Kernels.Rdsum
