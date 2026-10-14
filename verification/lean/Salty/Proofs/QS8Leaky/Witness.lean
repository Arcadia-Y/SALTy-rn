import Salty.Proofs.QS8Leaky.Correct

namespace Salty.Kernels.QS8Leaky
open CByte

/-- A nonempty admitted caller exercising both multiplier choices. Inputs +1
and -1 select distinct positive/negative slopes and yield +127 and -64. -/
def witnessCall : Call := ⟨2, 16#64, 32#64, 48#64, 0, 32768, 16384, 0⟩
def witnessState : State :=
  ⟨fun name =>
    if name = "batch" then some (.integer 2)
    else if name = "input" then some (.pointer 16#64)
    else if name = "output" then some (.pointer 32#64)
    else if name = "params" then some (.pointer 48#64)
    else none,
    ⟨fun a => if a = 16#64 then 1 else if a = 17#64 then 255
      else if a = 53#64 then 128 else if a = 57#64 then 64 else 0,
      fun _ => true, fun _ => true⟩⟩

private theorem disjoint_witness (base : Address) (h : base = 16#64 ∨ base = 48#64) :
    ∀ a, Footprint base (if base = 16#64 then 9 else 16) a → ¬ Footprint (32#64) 2 a := by
  intro a ⟨i, hi, hai⟩ ⟨j, hj, haj⟩
  have hn := congrArg BitVec.toNat (hai.symm.trans haj)
  rcases h with rfl | rfl <;> simp [BitVec.toNat_add, BitVec.toNat_ofNat] at hn hi <;> omega

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

theorem witness_positive : neonLane witnessCall.values 1 = 127 := by decide
theorem witness_negative : neonLane witnessCall.values 255 = 192 := by decide

end Salty.Kernels.QS8Leaky
