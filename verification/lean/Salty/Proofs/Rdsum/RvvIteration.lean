import Salty.Proofs.Rdsum.RvvGroup

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

structure GroupLocals (s : State) (pointers : Nat → Address) (zero : Address)
    (remaining : Int) (n increment : Nat) (acc : List (BitVec 16)) : Prop where
  rows : ∀ i, i < 7 → s.locals (rowName i) = some (.pointer (pointers i))
  zero : s.locals "zero" = some (.pointer zero)
  remaining : s.locals "current_batch" = some (.integer remaining)
  vl : s.locals "vl" = some (.integer n)
  increment : s.locals "input_increment" = some (.integer increment)
  acc : s.locals "vacc16" = some (.halfwords acc)

def groupRows (m : Memory) (pointers : Nat → Address) (zero : Address) (remaining : Int) (n : Nat) :
    Nat → List Byte := fun i => readBytes m (selectedPointers pointers remaining zero i) n

def groupPointers (pointers : Nat → Address) (zero : Address) (remaining : Int) (increment : Nat) :
    Nat → Address := fun i => selectedPointers pointers remaining zero i+BitVec.ofNat 64 increment

theorem rowName_ne_remaining (i : Nat) : rowName i ≠ "current_batch" := by
  unfold rowName
  split <;> decide

/-- Complete single iteration of the extracted RVV for-loop. -/
theorem rvv_iteration_exec (kind : Interpretation) (cfg : Config) (s : State)
    (pointers : Nat → Address) (zero : Address) (remaining : Int) (n increment : Nat)
    (acc : List (BitVec 16)) (cap : n ≤ cfg.capacity) (ha : acc.length = n)
    (lo : 0 < remaining) (hi : remaining ≤ 252)
    (loc : GroupLocals s pointers zero remaining n increment acc)
    (safe : ∀ i, i < 7 → ∀ a,
      Footprint (selectedPointers pointers remaining zero i) n a → s.memory.readable a = true) :
    ∃ t, Exec cfg (rvvIteration kind) s t ∧ t.memory = s.memory ∧
      GroupLocals t (groupPointers pointers zero remaining increment) zero (remaining-7) n increment
        (rowAcc kind (groupRows s.memory pointers zero remaining n) acc 7) := by
  obtain ⟨u,body,mem,accum,ptrs⟩ := rvv_group_exec kind cfg s pointers zero remaining n increment acc
    cap ha loc.rows loc.vl loc.acc loc.zero loc.remaining loc.increment safe
  have rem : u.locals "current_batch" = some (.integer remaining) :=
    (body.locals_frame "current_batch" (by cases kind <;> rfl)).trans loc.remaining
  let t := update u "current_batch" (.integer (remaining-7))
  have step : Exec cfg (.assign "current_batch" (.checkedSigned32
      (.bin .sub (.var "current_batch") (.lit 7)))) u t :=
    group_decrement_exec cfg u remaining rem lo hi
  have iteration : Exec cfg (rvvIteration kind) s t := by
    rw [rvv_iteration_shape]
    exact .seq body step
  refine ⟨t,iteration,mem,?_⟩
  constructor
  · intro i hi
    simpa only [t, update, rowName_ne_remaining i, ↓reduceIte, groupPointers] using ptrs i hi
  · exact (iteration.locals_frame "zero" (by cases kind <;> rfl)).trans loc.zero
  · simp [t, update]
  · exact (iteration.locals_frame "vl" (by cases kind <;> rfl)).trans loc.vl
  · exact (iteration.locals_frame "input_increment" (by cases kind <;> rfl)).trans loc.increment
  · simpa [t, update, groupRows] using accum

end Salty.Kernels.Rdsum
