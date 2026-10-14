import Salty.Proofs.Rdsum.RvvIteration

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

/-- Number of remaining seven-row groups, including a possibly partial last one. -/
def GroupCount (count : Nat) (remaining : Int) : Prop :=
  remaining ≤ 7*(count : Int) ∧ (count = 0 ∨ 7*((count-1 : Nat) : Int) < remaining)

theorem GroupCount.positive {count : Nat} {remaining : Int}
    (h : GroupCount (count+1) remaining) : 0 < remaining := by
  simp only [GroupCount, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, false_or] at h
  omega

theorem GroupCount.next {count : Nat} {remaining : Int}
    (h : GroupCount (count+1) remaining) : GroupCount count (remaining-7) := by
  unfold GroupCount at *
  cases count <;> simp_all <;> omega

/-- Read permissions for the recursive pointer substitutions. This predicate
is independent of arithmetic results and is discharged from memory geometry. -/
def GroupsSafe (m : Memory) (zero : Address) (n increment : Nat) :
    Nat → (Nat → Address) → Int → Prop
  | 0, _, _ => True
  | count+1, pointers, remaining =>
      (∀ i, i < 7 → ∀ a, Footprint (selectedPointers pointers remaining zero i) n a → m.readable a = true) ∧
      GroupsSafe m zero n increment count (groupPointers pointers zero remaining increment) (remaining-7)

structure GroupResult where
  pointers : Nat → Address
  remaining : Int
  acc : List (BitVec 16)

/-- Scalar schedule of the actual seven-row groups. Later memory lemmas relate
its selected row vectors to the original input columns and zero padding. -/
def groupFold (kind : Interpretation) (m : Memory) (zero : Address) (n increment : Nat) :
    Nat → (Nat → Address) → Int → List (BitVec 16) → GroupResult
  | 0, pointers, remaining, acc => ⟨pointers,remaining,acc⟩
  | count+1, pointers, remaining, acc => groupFold kind m zero n increment count
      (groupPointers pointers zero remaining increment) (remaining-7)
      (rowAcc kind (groupRows m pointers zero remaining n) acc 7)

def rvvInnerLoop (kind : Interpretation) : Stmt :=
  match kind with
  | .signed => firstStatement (dropStatements 1 (firstStatement (dropStatements 1 (rvvBatches kind))))
  | .unsigned => firstStatement (dropStatements 3 (rvvBatches kind))

theorem rvv_inner_shape (kind : Interpretation) : rvvInnerLoop kind =
    .loop (.bin .gt (.var "current_batch") (.lit 0)) (rvvIteration kind) := by
  cases kind <;> rfl

/-- Unbounded big-step execution of the actual seven-row loop. No fuel bound is
assumed; count is the mathematically determined number of groups. -/
theorem rvv_inner_total (kind : Interpretation) (cfg : Config) (s : State) (count : Nat)
    (pointers : Nat → Address) (zero : Address) (remaining : Int) (n increment : Nat)
    (acc : List (BitVec 16)) (cap : n ≤ cfg.capacity) (ha : acc.length = n)
    (counted : GroupCount count remaining) (hi : remaining ≤ 252)
    (loc : GroupLocals s pointers zero remaining n increment acc)
    (safe : GroupsSafe s.memory zero n increment count pointers remaining) :
    ∃ t, Exec cfg (rvvInnerLoop kind) s t ∧ t.memory = s.memory ∧
      let result := groupFold kind s.memory zero n increment count pointers remaining acc
      GroupLocals t result.pointers zero result.remaining n increment result.acc := by
  induction count generalizing s pointers remaining acc with
  | zero =>
    refine ⟨s,?_,rfl,loc⟩
    rw [rvv_inner_shape]
    have done : remaining ≤ 0 := by simpa [GroupCount] using counted.1
    apply Exec.done (v := .integer 0)
    · simp [eval, loc.remaining, binary, show ¬ remaining > 0 by omega]
    · rfl
  | succ count ih =>
    have positive := counted.positive
    obtain ⟨u,step,mem,uloc⟩ := rvv_iteration_exec kind cfg s pointers zero remaining n increment acc cap ha
      positive hi loc safe.1
    have len : (rowAcc kind (groupRows s.memory pointers zero remaining n) acc 7).length = n :=
      rowAcc_length kind _ acc n ha (fun i => readBytes_length ..) 7
    have nextSafe : GroupsSafe u.memory zero n increment count
        (groupPointers pointers zero remaining increment) (remaining-7) := by rw [mem]; exact safe.2
    obtain ⟨t,rest,tmem,tloc⟩ := ih u _ (remaining-7) _ len counted.next (by omega) uloc nextSafe
    refine ⟨t,?_,tmem.trans mem,?_⟩
    · rw [rvv_inner_shape]
      apply Exec.more (v := .integer 1) (t := u)
      · simp [eval, loc.remaining, binary, positive]
      · rfl
      · exact step
      · simpa only [← rvv_inner_shape] using rest
    · simpa only [groupFold, mem] using tloc

end Salty.Kernels.Rdsum
