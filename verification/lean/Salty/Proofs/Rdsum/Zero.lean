import Salty.Proofs.Core.CByteSyntax
import Salty.Generated.QS8RdsumRvv
import Salty.Generated.QU8RdsumRvv

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def rvvProgram : Interpretation → Stmt
  | .signed => Generated.QS8Rdsum.rvv
  | .unsigned => Generated.QU8Rdsum.rvv

def rvvChannels (kind : Interpretation) : Stmt :=
  loopBody (firstStatement (dropStatements 5 (rvvProgram kind)))

def rvvBatches (kind : Interpretation) : Stmt :=
  loopBody (firstStatement (dropStatements 10 (rvvChannels kind)))

def rvvGroup (kind : Interpretation) : Stmt :=
  match kind with
  | .signed => firstStatement (loopBody (firstStatement (dropStatements 1
      (firstStatement (dropStatements 1 (rvvBatches kind))))))
  | .unsigned => firstStatement (loopBody (firstStatement (dropStatements 3 (rvvBatches kind))))

/-- One exact source condition: the odd row numbers use `<`, the even ones `≤`. -/
def zeroBranch (name : String) (strict : Bool) (cutoff : Int) : Stmt :=
  .branch (.bin (if strict then .lt else .le) (.var "current_batch") (.lit cutoff))
    (.seq (.assign name (.var "zero")) .skip) .skip

def zeroWhen (strict : Bool) (r cutoff : Int) : Prop :=
  if strict then r < cutoff else r ≤ cutoff
instance (strict : Bool) (r cutoff : Int) : Decidable (zeroWhen strict r cutoff) :=
  inferInstanceAs (Decidable (if strict then r < cutoff else r ≤ cutoff))

def zeroAfter (s : State) (name : String) (strict : Bool) (cutoff r : Int) (z : Address) : State :=
  if zeroWhen strict r cutoff then update s name (.pointer z) else s

theorem zero_branch_exec (cfg : Config) (s : State) (name : String) (strict : Bool)
    (cutoff r : Int) (z : Address)
    (hr : s.locals "current_batch" = some (.integer r))
    (hz : s.locals "zero" = some (.pointer z)) :
    Exec cfg (zeroBranch name strict cutoff) s (zeroAfter s name strict cutoff r z) := by
  apply run_sound (fuel := 5)
  cases strict <;> simp only [zeroBranch, zeroAfter, zeroWhen, Bool.false_eq_true, ↓reduceIte]
  · by_cases h : r ≤ cutoff <;> simp [run, eval, binary, truth, hr, hz, h]
  · by_cases h : r < cutoff <;> simp [run, eval, binary, truth, hr, hz, h]

@[simp] theorem zeroAfter_memory (s : State) (name : String) (strict : Bool) (cutoff r : Int) (z : Address) :
    (zeroAfter s name strict cutoff r z).memory = s.memory := by
  unfold zeroAfter
  split <;> rfl

theorem zeroAfter_frame (s : State) (name query : String) (strict : Bool) (cutoff r : Int)
    (z : Address) (other : query ≠ name) :
    (zeroAfter s name strict cutoff r z).locals query = s.locals query := by
  unfold zeroAfter
  split <;> simp [update, other]

theorem zeroAfter_locals (s : State) (name query : String) (strict : Bool) (cutoff r : Int)
    (z : Address) :
    (zeroAfter s name strict cutoff r z).locals query =
      if zeroWhen strict r cutoff ∧ query = name then some (.pointer z) else s.locals query := by
  unfold zeroAfter
  split <;> simp_all [update]

def zeroBranches : Stmt :=
  .seq (zeroBranch "i1" true 2) (.seq (zeroBranch "i2" false 2)
  (.seq (zeroBranch "i3" true 4) (.seq (zeroBranch "i4" false 4)
  (.seq (zeroBranch "i5" true 6) (.seq (zeroBranch "i6" false 6) .skip)))))

theorem rvv_zero_shape (kind : Interpretation) : takeStatements 6 (rvvGroup kind) = zeroBranches := by
  cases kind <;> rfl

def zerosAfter (s : State) (r : Int) (z : Address) : State :=
  let s := zeroAfter s "i1" true 2 r z
  let s := zeroAfter s "i2" false 2 r z
  let s := zeroAfter s "i3" true 4 r z
  let s := zeroAfter s "i4" false 4 r z
  let s := zeroAfter s "i5" true 6 r z
  zeroAfter s "i6" false 6 r z

theorem zeros_exec (cfg : Config) (s : State) (r : Int) (z : Address)
    (hr : s.locals "current_batch" = some (.integer r))
    (hz : s.locals "zero" = some (.pointer z)) :
    Exec cfg zeroBranches s (zerosAfter s r z) := by
  unfold zeroBranches zerosAfter
  repeat' apply Exec.seq (zero_branch_exec cfg _ _ _ _ r z ?_ ?_)
  all_goals
    first
    | exact .skip
    | simp [zeroAfter_frame, hr, hz]

def rowName : Nat → String
  | 0 => "i0" | 1 => "i1" | 2 => "i2" | 3 => "i3"
  | 4 => "i4" | 5 => "i5" | 6 => "i6" | _ => "invalid-row"

@[simp] theorem zerosAfter_memory (s : State) (r : Int) (z : Address) :
    (zerosAfter s r z).memory = s.memory := by simp [zerosAfter]

/-- Exactly the unavailable rows are redirected. Row zero remains live because
the enclosing loop admits only a positive current batch. -/
theorem zerosAfter_row (s : State) (r : Int) (z : Address) (i : Nat) (hi : i < 7) :
    (zerosAfter s r z).locals (rowName i) =
      if 0 < i ∧ r ≤ (i : Int) then some (.pointer z) else s.locals (rowName i) := by
  have h1 : r < 2 ↔ r ≤ 1 := by omega
  have h3 : r < 4 ↔ r ≤ 3 := by omega
  have h5 : r < 6 ↔ r ≤ 5 := by omega
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [zerosAfter, zeroAfter_locals, zeroWhen, rowName, h1, h3, h5]

end Salty.Kernels.Rdsum
