import Salty.Proofs.Rdsum.NeonTailGroup

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

/-- Unbounded big-step execution of the actual seven-row loop. No fuel bound is
assumed; count is the mathematically determined number of groups. -/
theorem neon_tail_inner_total (kind : Interpretation) (cfg : Config) (s : State) (count : Nat)
    (pointers : Nat → Address) (zero : Address) (remaining : Int) (increment : Nat)
    (acc : List (BitVec 16)) (ha : acc.length = 8)
    (counted : GroupCount count remaining) (hi : remaining ≤ 252)
    (loc : NeonTailLocals kind s pointers zero remaining increment acc)
    (safe : GroupsSafe s.memory zero 8 increment count pointers remaining) :
    ∃ t, Exec cfg (neonInnerLoop kind false) s t ∧ t.memory = s.memory ∧
      let result := groupFold kind s.memory zero 8 increment count pointers remaining acc
      NeonTailLocals kind t result.pointers zero result.remaining increment result.acc := by
  induction count generalizing s pointers remaining acc with
  | zero =>
    refine ⟨s,?_,rfl,loc⟩
    rw [neon_inner_shape]
    have done : remaining ≤ 0 := by simpa [GroupCount] using counted.1
    apply Exec.done (v := .integer 0)
    · simp [eval, neonCurrent, loc.remaining, binary, show ¬ remaining > 0 by omega]
    · rfl
  | succ count ih =>
    have positive := counted.positive
    obtain ⟨u,step,mem,uloc⟩ := neon_tail_iteration_exec kind cfg s pointers zero remaining increment acc ha
      positive hi loc safe.1
    have len : (rowAcc kind (groupRows s.memory pointers zero remaining 8) acc 7).length = 8 :=
      rowAcc_length kind _ acc 8 ha (fun i => readBytes_length ..) 7
    have nextSafe : GroupsSafe u.memory zero 8 increment count
        (groupPointers pointers zero remaining increment) (remaining-7) := by rw [mem]; exact safe.2
    obtain ⟨t,rest,tmem,tloc⟩ := ih u _ (remaining-7) _ len counted.next (by omega) uloc nextSafe
    refine ⟨t,?_,tmem.trans mem,?_⟩
    · rw [neon_inner_shape]
      apply Exec.more (v := .integer 1) (t := u)
      · simp [eval, neonCurrent, loc.remaining, binary, positive]
      · rfl
      · simpa only [neonTailIteration, neon_inner_shape, loopBody] using step
      · simpa only [← neon_inner_shape] using rest
    · simpa only [groupFold, mem] using tloc


end Salty.Kernels.Rdsum
