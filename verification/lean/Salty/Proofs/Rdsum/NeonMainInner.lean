import Salty.Proofs.Rdsum.NeonMainGroup

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

theorem NeonMainLocals.set_current {kind : Interpretation} {s : State} {pointers : Nat → Address}
    {zero : Address} {remaining : Int} {increment : Nat} {acc : Nat → List (BitVec 16)}
    (loc : NeonMainLocals kind s pointers zero remaining increment acc) (next : Int) :
    NeonMainLocals kind (update s "current_batch" (.integer next)) pointers zero next increment acc := by
  constructor
  · intro i hi
    have hp := loc.rows i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [update, rowName] using hp
  · simpa [update] using loc.zero
  · simp [update]
  · simpa [update] using loc.increment
  · intro j hj
    have h := loc.acc j hj
    cases kind with
    | signed =>
      have cases : j = 0 ∨ j = 1 := by simp [neonChunks, neonWidth] at hj; omega
      rcases cases with rfl | rfl <;> simpa [update, neonHalfName] using h
    | unsigned =>
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [neonChunks, neonWidth] at hj; omega
      rcases cases with rfl | rfl | rfl | rfl <;> simpa [update, neonHalfName] using h

def neonMainIteration (kind : Interpretation) : Stmt := loopBody (neonInnerLoop kind true)

theorem neon_main_iteration_exec (kind : Interpretation) (cfg : Config) (s : State)
    (pointers : Nat → Address) (zero : Address) (remaining : Int) (increment : Nat)
    (acc : Nat → List (BitVec 16)) (ha : ∀ j, j < neonChunks kind true → (acc j).length = 8)
    (positive : 0 < remaining) (bound : remaining ≤ 252)
    (loc : NeonMainLocals kind s pointers zero remaining increment acc)
    (safe : ∀ i, i < 7 → ∀ a,
      Footprint (selectedPointers pointers remaining zero i) (mainReadSpan kind) a → s.memory.readable a = true) :
    ∃ t, Exec cfg (neonMainIteration kind) s t ∧ t.memory = s.memory ∧
      NeonMainLocals kind t (groupPointers pointers zero remaining increment) zero (remaining-7) increment
        (mainRowsAcc kind s.memory (selectedPointers pointers remaining zero) acc 7) := by
  obtain ⟨u,group,mem,uloc⟩ := neon_main_group_exec kind cfg s pointers zero remaining increment acc ha loc safe
  let t := update u "current_batch" (.integer (remaining-7))
  have step : Exec cfg (.assign "current_batch" (.checkedSigned32 (.bin .sub (.var "current_batch") (.lit 7)))) u t := by
    exact .assign (checked_sub_eval cfg u _ _ remaining 7 (by simpa only [eval] using uloc.remaining) (by simp only [eval]) (by omega))
  refine ⟨t,?_,mem,uloc.set_current (remaining-7)⟩
  unfold neonMainIteration
  rw [neon_inner_shape]
  exact .seq group step

structure MainFoldResult where
  pointers : Nat → Address
  remaining : Int
  acc : Nat → List (BitVec 16)

/-- Shared seven-row schedule with the source's two/four independent chunks. -/
def mainFold (kind : Interpretation) (m : Memory) (zero : Address) (increment : Nat) :
    Nat → (Nat → Address) → Int → (Nat → List (BitVec 16)) → MainFoldResult
  | 0, pointers, remaining, acc => ⟨pointers,remaining,acc⟩
  | count+1, pointers, remaining, acc =>
    mainFold kind m zero increment count (groupPointers pointers zero remaining increment) (remaining-7)
      (mainRowsAcc kind m (selectedPointers pointers remaining zero) acc 7)

/-- Unbounded execution of the main seven-row loop, preserving all chunks. -/
theorem neon_main_inner_total (kind : Interpretation) (cfg : Config) (s : State) (count : Nat)
    (pointers : Nat → Address) (zero : Address) (remaining : Int) (increment : Nat)
    (acc : Nat → List (BitVec 16)) (ha : ∀ j, j < neonChunks kind true → (acc j).length = 8)
    (counted : GroupCount count remaining) (hi : remaining ≤ 252)
    (loc : NeonMainLocals kind s pointers zero remaining increment acc)
    (safe : GroupsSafe s.memory zero (mainReadSpan kind) increment count pointers remaining) :
    ∃ t, Exec cfg (neonInnerLoop kind true) s t ∧ t.memory = s.memory ∧
      let result := mainFold kind s.memory zero increment count pointers remaining acc
      NeonMainLocals kind t result.pointers zero result.remaining increment result.acc := by
  induction count generalizing s pointers remaining acc with
  | zero =>
    refine ⟨s,?_,rfl,loc⟩
    rw [neon_inner_shape]
    have done : remaining ≤ 0 := by simpa [GroupCount] using counted.1
    apply Exec.done (v := .integer 0)
    · simp [eval, neonCurrent, loc.remaining, binary, show ¬ remaining > 0 by omega]
    · rfl
  | succ count ih =>
    obtain ⟨u,step,mem,uloc⟩ := neon_main_iteration_exec kind cfg s pointers zero remaining increment acc ha counted.positive hi loc safe.1
    have lengths : ∀ j, j < neonChunks kind true →
        (mainRowsAcc kind s.memory (selectedPointers pointers remaining zero) acc 7 j).length = 8 := by
      intro j hj
      exact rowAcc_length kind _ (acc j) 8 (ha j hj) (fun _ => readBytes_length ..) 7
    have nextSafe : GroupsSafe u.memory zero (mainReadSpan kind) increment count
        (groupPointers pointers zero remaining increment) (remaining-7) := by rw [mem]; exact safe.2
    obtain ⟨t,rest,tmem,tloc⟩ := ih u _ (remaining-7) _ lengths counted.next (by omega) uloc nextSafe
    refine ⟨t,?_,tmem.trans mem,?_⟩
    · rw [neon_inner_shape]
      apply Exec.more (v := .integer 1) (t := u)
      · simp [eval, neonCurrent, loc.remaining, binary, counted.positive]
      · rfl
      · simpa only [neonMainIteration, neon_inner_shape, loopBody] using step
      · simpa only [← neon_inner_shape] using rest
    · simpa only [mainFold, mem] using tloc

end Salty.Kernels.Rdsum
