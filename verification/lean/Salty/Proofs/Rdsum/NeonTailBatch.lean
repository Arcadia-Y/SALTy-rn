import Salty.Proofs.Rdsum.NeonTailWiden
import Salty.Proofs.Rdsum.NeonBatchInit

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

structure NeonTailBatchLocals (s : State) (pointers : Nat → Address) (zero : Address)
    (remaining stride : Nat) (acc : Nat → BitVec 32) : Prop where
  rows : ∀ i, i < 7 → s.locals (neonRowName false i) = some (.pointer (pointers i))
  zero : s.locals "zero" = some (.pointer zero)
  remaining : s.locals "r_2" = some (.integer remaining)
  increment : s.locals "input_increment" = some (.integer (7*stride))
  low : s.locals "vacc0_2" = some (.words32 (((List.range 8).map acc).take 4))
  high : s.locals "vacc1" = some (.words32 (((List.range 8).map acc).drop 4))

def neonTailStarted (kind : Interpretation) (s : State) (remaining : Nat) : State :=
  update (update s (neonHalfName kind false 0) (.halfwords (List.replicate 8 0)))
    "current_batch_2" (.integer (batchSize remaining))

theorem neon_tail_start_exec (kind : Interpretation) (cfg : Config) (s : State)
    (remaining : Nat) (bound : remaining < 2^31)
    (hr : s.locals "r_2" = some (.integer remaining)) :
    Exec cfg (.seq (neonTailReset kind) (neonCount kind false)) s (neonTailStarted kind s remaining) := by
  apply Exec.seq (neon_tail_reset_exec kind cfg s)
  apply neon_count_exec kind false cfg _ remaining bound
  cases kind <;> simpa [update, neonRemaining, neonHalfName] using hr

private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

theorem neonTailStarted_group (kind : Interpretation) (s : State) (pointers : Nat → Address) (zero : Address)
    (remaining stride : Nat) (initial : Nat → BitVec 32)
    (loc : NeonTailBatchLocals s pointers zero remaining stride initial) :
    NeonTailLocals kind (neonTailStarted kind s remaining) pointers zero (batchSize remaining) (7*stride)
      ((List.range 8).map (fun _ => 0)) := by
  cases kind <;> constructor
  all_goals try { simp [neonTailStarted, update_locals, neonHalfName, loc.zero, loc.increment, List.map_const'] }
  all_goals
    intro i hi
    have hp := loc.rows i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [neonTailStarted, update_locals, neonHalfName, neonRowName] using hp

theorem neon_tail_batch_compose (kind : Interpretation) (cfg : Config) (s u v t : State)
    (start : Exec cfg (.seq (neonTailReset kind) (neonCount kind false)) s u)
    (middle : Exec cfg (.seq (neonInnerLoop kind false) (neonTailWiden kind)) u v)
    (finish : Exec cfg (neonFinish kind false) v t) : Exec cfg (neonBatch kind false) s t := by
  have shape : neonBatch kind false = .seq (neonTailReset kind)
      (.seq (.seq (neonCount kind false) (neonInnerLoop kind false))
        (.seq (firstStatement (neonTailWiden kind))
          (.seq (firstStatement (dropStatements 1 (neonTailWiden kind))) (.seq (neonFinish kind false) .skip)))) := by
    cases kind <;> rfl
  rw [shape]
  cases start with
  | seq reset count =>
    cases middle with
    | seq loop wide =>
      rw [neon_tail_widen_shape] at wide
      cases wide with
      | seq lo rest =>
        cases rest with
        | seq hi done =>
          cases done
          apply Exec.seq reset (Exec.seq (.seq count loop) ?_)
          cases kind <;> exact .seq lo (.seq hi (.seq finish .skip))

theorem neon_tail_batch_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero : Address) (stride first remaining : Nat) (pointers : Nat → Address)
    (initial : Nat → BitVec 32) (positive : 0 < remaining) (bound : remaining < 2^31)
    (loc : NeonTailBatchLocals s pointers zero remaining stride initial)
    (safe : GroupsSafe s.memory zero 8 (7*stride) ((batchSize remaining+6)/7) pointers (batchSize remaining))
    (zeros : ∀ column, column < 8 → s.memory.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < batchSize remaining → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∃ t, Exec cfg (neonBatch kind false) s t ∧ t.memory = s.memory ∧
      NeonTailBatchLocals t
        (groupFold kind s.memory zero 8 (7*stride) ((batchSize remaining+6)/7)
          pointers (batchSize remaining) ((List.range 8).map (fun _ => 0))).pointers
        zero (remaining-batchSize remaining) stride
        (fun column => initial column+intervalSum kind s.memory input stride first (batchSize remaining) column) := by
  let u := neonTailStarted kind s remaining
  have start : Exec cfg (.seq (neonTailReset kind) (neonCount kind false)) s u :=
    neon_tail_start_exec kind cfg s remaining bound loc.remaining
  have umem : u.memory = s.memory := by cases kind <;> rfl
  have lo : u.locals "vacc0_2" = s.locals "vacc0_2" := start.locals_frame _ (by cases kind <;> rfl)
  have hi : u.locals "vacc1" = s.locals "vacc1" := start.locals_frame _ (by cases kind <;> rfl)
  obtain ⟨v,middle,mem,low,high,rows⟩ := neon_tail_inner_widen_correct kind cfg u input zero stride first
    (batchSize remaining) pointers initial (by unfold batchSize; omega) (Nat.min_le_right ..)
    (neonTailStarted_group kind s pointers zero remaining stride initial loc)
    (lo.trans loc.low) (hi.trans loc.high) (by simpa only [umem] using safe) (by simpa only [umem] using zeros) ptrs
  rw [umem] at low high rows
  have vr : v.locals "r_2" = some (.integer remaining) :=
    ((middle.locals_frame _ (by cases kind <;> rfl)).trans (start.locals_frame _ (by cases kind <;> rfl))).trans loc.remaining
  let t := update v "r_2" (.integer (remaining-batchSize remaining : Nat))
  have finish : Exec cfg (neonFinish kind false) v t := neon_finish_exec kind false cfg v remaining bound vr
  have all : Exec cfg (neonBatch kind false) s t := neon_tail_batch_compose kind cfg s u v t start middle finish
  refine ⟨t,all,mem.trans umem,?_⟩
  constructor
  · intro i hi
    have hp := rows i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [t, update_locals, neonRowName] using hp
  · exact (all.locals_frame "zero" (by cases kind <;> rfl)).trans loc.zero
  · simp [t, update_locals]
  · exact (all.locals_frame "input_increment" (by cases kind <;> rfl)).trans loc.increment
  · exact (finish.locals_frame "vacc0_2" (by cases kind <;> rfl)).trans low
  · exact (finish.locals_frame "vacc1" (by cases kind <;> rfl)).trans high

end Salty.Kernels.Rdsum
