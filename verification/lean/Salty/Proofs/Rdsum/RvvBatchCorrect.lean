import Salty.Proofs.Rdsum.RvvBatchStart

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def startRemaining (kind : Interpretation) (remaining : Nat) : Nat :=
  match kind with
  | .signed => remaining
  | .unsigned => remaining-batchSize remaining

def batchFinish : Interpretation → Stmt
  | .signed => rvvFinish
  | .unsigned => .skip

def batchFinished (kind : Interpretation) (s : State) (remaining : Nat) : State :=
  match kind with
  | .signed => update s "r" (.integer (remaining-batchSize remaining : Nat))
  | .unsigned => s

theorem rvv_batches_shape (kind : Interpretation) : rvvBatches kind =
    match kind with
    | .signed => .seq (rvvReset kind) (.seq (.seq (rvvCount kind) (rvvInnerLoop kind))
        (.seq (rvvWiden kind) (.seq rvvFinish .skip)))
    | .unsigned => .seq (rvvReset kind) (.seq (rvvCount kind) (.seq rvvSubtract
        (.seq (rvvInnerLoop kind) (.seq (rvvWiden kind) .skip)))) := by
  cases kind <;> rfl

theorem batch_compose (kind : Interpretation) (cfg : Config) (s u v t : State)
    (start : Exec cfg (batchStart kind) s u)
    (middle : Exec cfg (.seq (rvvInnerLoop kind) (rvvWiden kind)) u v)
    (finish : Exec cfg (batchFinish kind) v t) :
    Exec cfg (rvvBatches kind) s t := by
  cases middle with
  | seq loop wide =>
    cases start with
    | seq reset rest =>
      cases rest with
      | seq count adjust =>
        rw [rvv_batches_shape]
        cases kind with
        | signed =>
          cases adjust
          exact .seq reset (.seq (.seq count loop) (.seq wide (.seq finish .skip)))
        | unsigned =>
          cases finish
          exact .seq reset (.seq count (.seq adjust (.seq loop (.seq wide .skip))))

@[simp] theorem batchFinished_memory (kind : Interpretation) (s : State) (remaining : Nat) :
    (batchFinished kind s remaining).memory = s.memory := by cases kind <;> rfl

theorem batch_finish_exec (kind : Interpretation) (cfg : Config) (s : State) (remaining : Nat)
    (bound : remaining < 2^31)
    (hr : s.locals "r" = some (.integer
      (startRemaining kind remaining))) :
    Exec cfg (batchFinish kind) s (batchFinished kind s remaining) := by
  cases kind with
  | signed => exact rvv_finish_exec cfg s remaining bound hr
  | unsigned => exact .skip

/-- One complete extracted batch, including the different signed/unsigned
placement of the remaining-row update. -/
theorem rvv_batch_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero : Address) (width stride first remaining : Nat) (pointers : Nat → Address)
    (initial : Nat → BitVec 32) (positive : 0 < remaining) (bound : remaining < 2^31)
    (cap : width ≤ cfg.capacity) (loc : BatchLocals kind s pointers zero remaining width stride initial)
    (safe : GroupsSafe s.memory zero width (7*stride) ((batchSize remaining+6)/7)
      pointers (batchSize remaining))
    (zeros : ∀ column, column < width → s.memory.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < batchSize remaining →
      pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∃ t, Exec cfg (rvvBatches kind) s t ∧ t.memory = s.memory ∧
      BatchLocals kind t
        (groupFold kind s.memory zero width (7*stride) ((batchSize remaining+6)/7)
          pointers (batchSize remaining) ((List.range width).map (fun _ => 0))).pointers
        zero (remaining-batchSize remaining) width stride
        (fun column => initial column+intervalSum kind s.memory input stride first (batchSize remaining) column) := by
  let u := batchStarted kind s width remaining
  have start : Exec cfg (batchStart kind) s u := batch_start_exec kind cfg s width remaining cap bound loc.vl loc.remaining
  have sizePos : 0 < batchSize remaining := by unfold batchSize; omega
  have sizeBound : batchSize remaining ≤ 252 := Nat.min_le_right ..
  have umem : u.memory = s.memory := batchStarted_memory kind s width remaining
  obtain ⟨v,middle,mem,acc,rows⟩ := rvv_inner_widen_correct kind cfg u input zero width stride first
    (batchSize remaining) pointers initial sizePos sizeBound cap
    (batchStarted_group kind s pointers zero remaining width stride initial loc)
    ((batchStarted_acc kind s width remaining).trans loc.acc) (by simpa only [umem] using safe) (by simpa only [umem] using zeros) ptrs
  rw [umem] at acc rows
  have vr : v.locals "r" = some (.integer
      (startRemaining kind remaining)) :=
    (middle.locals_frame "r" (by cases kind <;> rfl)).trans (batchStarted_remaining kind s width remaining loc.remaining)
  let t := batchFinished kind v remaining
  have finish : Exec cfg (batchFinish kind) v t := batch_finish_exec kind cfg v remaining bound vr
  have all : Exec cfg (rvvBatches kind) s t := batch_compose kind cfg s u v t start middle finish
  refine ⟨t,all,?_,?_⟩
  · exact (batchFinished_memory kind v remaining).trans (mem.trans (batchStarted_memory kind s width remaining))
  · constructor
    · intro i hi
      exact (finish.locals_frame (rowName i) (by
        have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
        rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases kind <;> rfl)).trans (rows i hi)
    · exact (all.locals_frame "zero" (by cases kind <;> rfl)).trans loc.zero
    · cases kind <;> simpa [t, batchFinished, update, startRemaining] using vr
    · exact (all.locals_frame "vl" (by cases kind <;> rfl)).trans loc.vl
    · exact (all.locals_frame "input_increment" (by cases kind <;> rfl)).trans loc.increment
    · exact (finish.locals_frame (accumulatorName kind) (by cases kind <;> rfl)).trans acc

end Salty.Kernels.Rdsum
