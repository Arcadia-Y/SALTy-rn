import Salty.Proofs.Rdsum.RvvWiden

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def batchSize (remaining : Nat) : Nat := min remaining 252

def rvvReset (kind : Interpretation) : Stmt := firstStatement (rvvBatches kind)
def rvvCount (kind : Interpretation) : Stmt :=
  match kind with
  | .signed => firstStatement (firstStatement (dropStatements 1 (rvvBatches kind)))
  | .unsigned => firstStatement (dropStatements 1 (rvvBatches kind))
def rvvSubtract : Stmt := firstStatement (dropStatements 2 (rvvBatches .unsigned))
def rvvFinish : Stmt := firstStatement (dropStatements 3 (rvvBatches .signed))

theorem rvv_reset_shape (kind : Interpretation) : rvvReset kind =
    .assign "vacc16" (.call .dupI16RVV
      [.cast (match kind with | .signed => .i16 | .unsigned => .u16) (.lit 0), .var "vl"]) := by
  cases kind <;> rfl

theorem rvv_count_shape (kind : Interpretation) : rvvCount kind =
    .assign "current_batch" (.conditional (.bin .lt (.var "r") (.lit 252)) (.var "r") (.lit 252)) := by
  cases kind <;> rfl

theorem rvv_subtract_shape : rvvSubtract =
    .assign "r" (.checkedSigned32 (.bin .sub (.var "r") (.var "current_batch"))) := rfl

theorem rvv_finish_shape : rvvFinish =
    .assign "r" (.conditional (.bin .gt (.var "r") (.lit 252))
      (.checkedSigned32 (.bin .sub (.var "r") (.lit 252))) (.lit 0)) := rfl

theorem rvv_reset_exec (kind : Interpretation) (cfg : Config) (s : State) (width : Nat)
    (cap : width ≤ cfg.capacity) (vl : s.locals "vl" = some (.integer width)) :
    Exec cfg (rvvReset kind) s (update s "vacc16" (.halfwords (List.replicate width 0))) := by
  rw [rvv_reset_shape]
  apply Exec.assign
  cases kind <;> simp [eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, convert, vl, cap]

theorem rvv_count_exec (kind : Interpretation) (cfg : Config) (s : State) (remaining : Nat)
    (hr : s.locals "r" = some (.integer remaining)) :
    Exec cfg (rvvCount kind) s (update s "current_batch" (.integer (batchSize remaining))) := by
  have chosen : batchSize remaining = if remaining < 252 then remaining else 252 := by
    by_cases h : remaining < 252
    · simp [batchSize, h, Nat.min_eq_left (by omega : remaining ≤ 252)]
    · simp [batchSize, h, Nat.min_eq_right (by omega : 252 ≤ remaining)]
  rw [rvv_count_shape]
  apply Exec.assign
  by_cases small : remaining < 252 <;>
    simp [eval, binary, truth, hr, chosen, small,
      show ((remaining : Int) < 252) ↔ remaining < 252 from by omega]

theorem checked_sub_eval (cfg : Config) (s : State) (a b : Expr) (x y : Int)
    (ha : eval cfg s a = some (.integer x)) (hb : eval cfg s b = some (.integer y))
    (bounds : -(2^31) ≤ x-y ∧ x-y < 2^31) :
    eval cfg s (.checkedSigned32 (.bin .sub a b)) = some (.integer (x-y)) := by
  simp only [eval, ha, hb, Option.bind_some, binary, bounds, ↓reduceIte, pure, bind]
  rfl

theorem rvv_subtract_exec (cfg : Config) (s : State) (remaining : Nat) (bound : remaining < 2^31)
    (hr : s.locals "r" = some (.integer remaining))
    (hc : s.locals "current_batch" = some (.integer (batchSize remaining))) :
    Exec cfg rvvSubtract s (update s "r" (.integer (remaining-batchSize remaining : Nat))) := by
  have small : batchSize remaining ≤ remaining := Nat.min_le_left ..
  have sub : (remaining : Int)-batchSize remaining = (remaining-batchSize remaining : Nat) := by omega
  have bounds : -(2147483648 : Int) ≤ (remaining : Int)-batchSize remaining ∧
      (remaining : Int)-batchSize remaining < 2147483648 := by omega
  rw [rvv_subtract_shape]
  apply Exec.assign
  have h := checked_sub_eval cfg s (.var "r") (.var "current_batch") remaining (batchSize remaining)
    (by simpa only [eval] using hr) (by simpa only [eval] using hc) (by simpa using bounds)
  rw [sub] at h
  exact h

theorem rvv_finish_exec (cfg : Config) (s : State) (remaining : Nat) (bound : remaining < 2^31)
    (hr : s.locals "r" = some (.integer remaining)) :
    Exec cfg rvvFinish s (update s "r" (.integer (remaining-batchSize remaining : Nat))) := by
  rw [rvv_finish_shape]
  apply Exec.assign
  by_cases large : 252 < remaining
  · have cond : (252 : Int) < remaining := by omega
    have bounds : -(2147483648 : Int) ≤ (remaining : Int)-252 ∧ (remaining : Int)-252 < 2147483648 := by omega
    have sub : (remaining : Int)-252 = (remaining-252 : Nat) := by omega
    have h := checked_sub_eval cfg s (.var "r") (.lit 252) remaining 252 (by simpa only [eval] using hr) (by simp only [eval]) (by simpa using bounds)
    have guard : eval cfg s (.bin .gt (.var "r") (.lit 252)) = some (.integer 1) := by
      simp [eval, binary, hr, cond]
    rw [eval, guard]
    change eval cfg s (.checkedSigned32 (.bin .sub (.var "r") (.lit 252))) = _
    rw [h, sub]
    simp [batchSize, Nat.min_eq_right (by omega : 252 ≤ remaining)]
  · have cond : ¬ (252 : Int) < remaining := by omega
    simp [eval, binary, truth, hr, cond,
      batchSize, Nat.min_eq_left (by omega : remaining ≤ 252)]

end Salty.Kernels.Rdsum
