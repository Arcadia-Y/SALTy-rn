import Salty.Proofs.Rdsum.RvvBatchInit

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

structure BatchLocals (kind : Interpretation) (s : State) (pointers : Nat → Address) (zero : Address)
    (remaining width stride : Nat) (acc : Nat → BitVec 32) : Prop where
  rows : ∀ i, i < 7 → s.locals (rowName i) = some (.pointer (pointers i))
  zero : s.locals "zero" = some (.pointer zero)
  remaining : s.locals "r" = some (.integer remaining)
  vl : s.locals "vl" = some (.integer width)
  increment : s.locals "input_increment" = some (.integer (7*stride))
  acc : s.locals (accumulatorName kind) = some (.words32 ((List.range width).map acc))

def batchAdjust : Interpretation → Stmt
  | .signed => .skip
  | .unsigned => rvvSubtract

def batchStart (kind : Interpretation) : Stmt :=
  .seq (rvvReset kind) (.seq (rvvCount kind) (batchAdjust kind))

def batchStarted (kind : Interpretation) (s : State) (width remaining : Nat) : State :=
  let s := update s "vacc16" (.halfwords (List.replicate width 0))
  let s := update s "current_batch" (.integer (batchSize remaining))
  match kind with
  | .signed => s
  | .unsigned => update s "r" (.integer (remaining-batchSize remaining : Nat))

private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

theorem batch_start_exec (kind : Interpretation) (cfg : Config) (s : State) (width remaining : Nat)
    (cap : width ≤ cfg.capacity) (bound : remaining < 2^31)
    (vl : s.locals "vl" = some (.integer width))
    (hr : s.locals "r" = some (.integer remaining)) :
    Exec cfg (batchStart kind) s (batchStarted kind s width remaining) := by
  let u := update s "vacc16" (.halfwords (List.replicate width 0))
  let v := update u "current_batch" (.integer (batchSize remaining))
  have reset : Exec cfg (rvvReset kind) s u := rvv_reset_exec kind cfg s width cap vl
  have ur : u.locals "r" = some (.integer remaining) := by simp [u, update_locals, hr]
  have count : Exec cfg (rvvCount kind) u v := rvv_count_exec kind cfg u remaining ur
  apply Exec.seq reset (Exec.seq count ?_)
  cases kind with
  | signed => exact .skip
  | unsigned =>
    exact rvv_subtract_exec cfg v remaining bound (by simp [v, u, update_locals, hr])
      (by simp [v, update_locals])

@[simp] theorem batchStarted_memory (kind : Interpretation) (s : State) (width remaining : Nat) :
    (batchStarted kind s width remaining).memory = s.memory := by cases kind <;> rfl

theorem batchStarted_group (kind : Interpretation) (s : State) (pointers : Nat → Address) (zero : Address)
    (remaining width stride : Nat) (acc : Nat → BitVec 32)
    (loc : BatchLocals kind s pointers zero remaining width stride acc) :
    GroupLocals (batchStarted kind s width remaining) pointers zero (batchSize remaining) width (7*stride)
      ((List.range width).map (fun _ => 0)) := by
  cases kind <;> constructor
  all_goals try { simp [batchStarted, update_locals, loc.zero, loc.vl, loc.increment, List.map_const'] }
  all_goals
    intro i hi
    have hp := loc.rows i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [batchStarted, update_locals, rowName] using hp

theorem batchStarted_acc (kind : Interpretation) (s : State) (width remaining : Nat) :
    (batchStarted kind s width remaining).locals (accumulatorName kind) = s.locals (accumulatorName kind) := by
  cases kind <;> simp [batchStarted, update_locals, accumulatorName]

theorem batchStarted_remaining (kind : Interpretation) (s : State) (width remaining : Nat)
    (hr : s.locals "r" = some (.integer remaining)) :
    (batchStarted kind s width remaining).locals "r" = some (.integer
      (match kind with | .signed => remaining | .unsigned => remaining-batchSize remaining : Nat)) := by
  cases kind <;> simp [batchStarted, update_locals, hr]

end Salty.Kernels.Rdsum
