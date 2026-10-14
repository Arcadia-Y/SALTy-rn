import Salty.Proofs.S8Clamp.Correct

namespace Salty.Kernels.S8Clamp.Execution
open CByte

/-- A concrete admitted call, making nonvacuity of Entry kernel-checkable.
All bytes initially zero; one input byte at 16 with padding, one output byte at
32, and the two aligned 32-bit clamp parameters at 48. -/
def witnessCall : Call := ⟨1, 16#64, 32#64, 48#64, 0, 0⟩
def witnessState : State :=
  ⟨fun name =>
    if name = "batch" then some (.integer 1)
    else if name = "input" then some (.pointer 16#64)
    else if name = "output" then some (.pointer 32#64)
    else if name = "params" then some (.pointer 48#64)
    else none,
    ⟨fun _ => 0, fun _ => true, fun _ => true⟩⟩

private theorem disjoint_witness (base : Address) (h : base = 16#64 ∨ base = 48#64) :
    ∀ a, Footprint base 8 a → ¬ Footprint (32#64) 1 a := by
  intro a ⟨i, hi, hai⟩ ⟨j, hj, haj⟩
  have hj0 : j = 0 := by omega
  subst j
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at haj
  rw [hai] at haj
  have hn := congrArg BitVec.toNat haj
  rcases h with rfl | rfl <;> simp [BitVec.toNat_add, BitVec.toNat_ofNat] at hn <;> omega

theorem entry_nonempty : Entry witnessState witnessCall := by
  constructor
  all_goals try { rfl }
  all_goals try { decide }
  · constructor
    · intro a ha; rfl
    · intro a ha; rfl
    · exact disjoint_witness _ (Or.inl rfl)
  · intro a ha; rfl
  · exact disjoint_witness _ (Or.inr rfl)
  · simp [Valid, Call.bounds, witnessCall]

end Salty.Kernels.S8Clamp.Execution
