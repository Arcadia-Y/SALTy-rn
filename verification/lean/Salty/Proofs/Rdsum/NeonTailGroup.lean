import Salty.Proofs.Rdsum.NeonTailData

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

structure NeonTailLocals (kind : Interpretation) (s : State) (pointers : Nat → Address) (zero : Address)
    (remaining : Int) (increment : Nat) (acc : List (BitVec 16)) : Prop where
  rows : ∀ i, i < 7 → s.locals (neonRowName false i) = some (.pointer (pointers i))
  zero : s.locals "zero" = some (.pointer zero)
  remaining : s.locals "current_batch_2" = some (.integer remaining)
  increment : s.locals "input_increment" = some (.integer increment)
  acc : s.locals (neonHalfName kind false 0) = some (.halfwords acc)

theorem neon_tail_group_exec (kind : Interpretation) (cfg : Config) (s : State)
    (pointers : Nat → Address) (zero : Address) (remaining : Int) (increment : Nat)
    (acc : List (BitVec 16)) (ha : acc.length = 8)
    (loc : NeonTailLocals kind s pointers zero remaining increment acc)
    (safe : ∀ i, i < 7 → ∀ a, Footprint (selectedPointers pointers remaining zero i) 8 a → s.memory.readable a = true) :
    ∃ t, Exec cfg (neonGroup kind false) s t ∧ t.memory = s.memory ∧
      NeonTailLocals kind t (groupPointers pointers zero remaining increment) zero remaining increment
        (rowAcc kind (groupRows s.memory pointers zero remaining 8) acc 7) := by
  let u := neonZerosAfter false s remaining zero
  have zeros : Exec cfg (neonZeroBranches false) s u := neon_zeros_exec cfg s false remaining zero loc.remaining loc.zero
  have umem : u.memory = s.memory := neonZerosAfter_memory false s remaining zero
  have ptrs : ∀ i, i < 7 → u.locals (neonRowName false i) = some (.pointer (selectedPointers pointers remaining zero i)) := by
    intro i hi
    rw [neonZerosAfter_row false s remaining zero i hi]
    by_cases absent : 0 < i ∧ remaining ≤ (i : Int) <;> simp [selectedPointers, absent, loc.rows i hi]
  have accum : u.locals (neonHalfName kind false 0) = some (.halfwords acc) :=
    (zeros.locals_frame _ (by cases kind <;> rfl)).trans loc.acc
  have step : u.locals "input_increment" = some (.integer increment) :=
    (zeros.locals_frame _ (by rfl)).trans loc.increment
  let t := neonTailDataAfter kind u (selectedPointers pointers remaining zero) increment
    (fun i => readBytes u.memory (selectedPointers pointers remaining zero i) 8) acc
  have data : Exec cfg (neonTailData kind) u t := neon_tail_data_exec kind cfg u _ increment acc ha ptrs accum step
    (by simpa only [umem] using safe)
  have body : Exec cfg (neonGroup kind false) s t := exec_take_drop 6
    (by rw [neon_zero_shape]; exact zeros) data
  refine ⟨t,body,(neonTailDataAfter_memory ..).trans umem,?_⟩
  constructor
  · intro i hi
    exact neonTailDataAfter_row kind u _ increment _ acc i hi
  · exact (body.locals_frame "zero" (by cases kind <;> rfl)).trans loc.zero
  · exact (body.locals_frame "current_batch_2" (by cases kind <;> rfl)).trans loc.remaining
  · exact (body.locals_frame "input_increment" (by cases kind <;> rfl)).trans loc.increment
  · simpa only [t, umem, groupRows] using neonTailDataAfter_acc kind u (selectedPointers pointers remaining zero) increment
      (fun i => readBytes u.memory (selectedPointers pointers remaining zero i) 8) acc

def neonTailIteration (kind : Interpretation) : Stmt := loopBody (neonInnerLoop kind false)

theorem neon_tail_iteration_exec (kind : Interpretation) (cfg : Config) (s : State)
    (pointers : Nat → Address) (zero : Address) (remaining : Int) (increment : Nat)
    (acc : List (BitVec 16)) (ha : acc.length = 8) (positive : 0 < remaining) (bound : remaining ≤ 252)
    (loc : NeonTailLocals kind s pointers zero remaining increment acc)
    (safe : ∀ i, i < 7 → ∀ a, Footprint (selectedPointers pointers remaining zero i) 8 a → s.memory.readable a = true) :
    ∃ t, Exec cfg (neonTailIteration kind) s t ∧ t.memory = s.memory ∧
      NeonTailLocals kind t (groupPointers pointers zero remaining increment) zero (remaining-7) increment
        (rowAcc kind (groupRows s.memory pointers zero remaining 8) acc 7) := by
  obtain ⟨u,body,mem,uloc⟩ := neon_tail_group_exec kind cfg s pointers zero remaining increment acc ha loc safe
  let t := update u "current_batch_2" (.integer (remaining-7))
  have step : Exec cfg (.assign "current_batch_2" (.checkedSigned32 (.bin .sub (.var "current_batch_2") (.lit 7)))) u t := by
    apply Exec.assign
    have bounds : -(2^31) ≤ remaining-7 ∧ remaining-7 < 2^31 := by omega
    simp [eval, binary, uloc.remaining, bounds]
    omega
  have iteration : Exec cfg (neonTailIteration kind) s t := by
    unfold neonTailIteration
    rw [neon_inner_shape]
    exact .seq body step
  refine ⟨t,iteration,mem,?_⟩
  constructor
  · intro i hi
    have hp := uloc.rows i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [t, update, neonRowName] using hp
  · exact (iteration.locals_frame "zero" (by cases kind <;> rfl)).trans loc.zero
  · simp [t, update]
  · exact (iteration.locals_frame "input_increment" (by cases kind <;> rfl)).trans loc.increment
  · cases kind <;> simpa [t, update, neonHalfName] using uloc.acc

end Salty.Kernels.Rdsum
