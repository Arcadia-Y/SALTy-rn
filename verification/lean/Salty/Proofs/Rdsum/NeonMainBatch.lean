import Salty.Proofs.Rdsum.NeonMainBatchInit

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

theorem neon_main_batch_compose (kind : Interpretation) (cfg : Config) (s u v t : State)
    (start : Exec cfg (.seq (mainReset kind) (neonCount kind true)) s u)
    (middle : Exec cfg (.seq (neonInnerLoop kind true) (neonMainWiden kind)) u v)
    (finish : Exec cfg (neonFinish kind true) v t) : Exec cfg (neonBatch kind true) s t := by
  have shape : neonBatch kind true = appendStatements (mainReset kind)
      (.seq (.seq (neonCount kind true) (neonInnerLoop kind true))
        (appendStatements (neonMainWiden kind) (.seq (neonFinish kind true) .skip))) := by cases kind <;> rfl
  rw [shape]
  cases start with
  | seq reset count =>
    cases middle with
    | seq loop wide =>
      exact appendStatements_exec reset (.seq (.seq count loop) (appendStatements_exec wide (.seq finish .skip)))

/-- Complete extracted main batch, including all reset accumulators and the
source min/doz casts; every word agrees with the original-memory row interval. -/
theorem neon_main_batch_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero : Address) (stride first remaining : Nat) (pointers : Nat → Address)
    (initial : Nat → BitVec 32) (positive : 0 < remaining) (bound : remaining < 2^31)
    (loc : NeonMainBatchLocals kind s pointers zero remaining stride initial)
    (safe : GroupsSafe s.memory zero (mainReadSpan kind) (7*stride) ((batchSize remaining+6)/7) pointers (batchSize remaining))
    (zeros : ∀ column, column < neonWidth kind true → s.memory.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < batchSize remaining → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∃ t, Exec cfg (neonBatch kind true) s t ∧ t.memory = s.memory ∧
      NeonMainBatchLocals kind t
        (mainFold kind s.memory zero (7*stride) ((batchSize remaining+6)/7)
          pointers (batchSize remaining) zeroMainAcc).pointers
        zero (remaining-batchSize remaining) stride
        (fun column => initial column+intervalSum kind s.memory input stride first (batchSize remaining) column) := by
  let u := mainStarted kind s remaining
  have start : Exec cfg (.seq (mainReset kind) (neonCount kind true)) s u := main_start_exec kind cfg s remaining bound loc.remaining
  have umem : u.memory = s.memory := mainStarted_memory kind s remaining
  have words : ∀ word, word < neonWidth kind true/4 →
      u.locals (neonWordName true word) = some (.words32 (wordValues initial word)) := by
    intro word hw
    have w8 : word < 8 := by cases kind <;> simp [neonWidth] at hw <;> omega
    exact (start.locals_frame _ (main_start_word_frame kind word w8)).trans (loc.words word hw)
  obtain ⟨v,middle,mem,values,rows⟩ := neon_main_inner_widen_correct kind cfg u input zero stride first
    (batchSize remaining) pointers initial (by unfold batchSize; omega) (Nat.min_le_right ..)
    (mainStarted_group kind s pointers zero remaining stride initial loc) words
    (by simpa only [umem] using safe) (by simpa only [umem] using zeros) ptrs
  rw [umem] at values rows
  have vr : v.locals "r" = some (.integer remaining) :=
    ((middle.locals_frame _ (by cases kind <;> rfl)).trans (start.locals_frame _ (by cases kind <;> rfl))).trans loc.remaining
  let t := update v "r" (.integer (remaining-batchSize remaining : Nat))
  have finish : Exec cfg (neonFinish kind true) v t := neon_finish_exec kind true cfg v remaining bound vr
  have all : Exec cfg (neonBatch kind true) s t := neon_main_batch_compose kind cfg s u v t start middle finish
  refine ⟨t,all,mem.trans umem,?_⟩
  constructor
  · intro i hi
    have hp := rows i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [t, update, rowName] using hp
  · exact (all.locals_frame _ (by cases kind <;> rfl)).trans loc.zero
  · simp [t, update]
  · exact (all.locals_frame _ (by cases kind <;> rfl)).trans loc.increment
  · intro word hw
    have w8 : word < 8 := by cases kind <;> simp [neonWidth] at hw <;> omega
    exact (finish.locals_frame _ (main_finish_word_frame kind word w8)).trans (values word hw)

end Salty.Kernels.Rdsum
