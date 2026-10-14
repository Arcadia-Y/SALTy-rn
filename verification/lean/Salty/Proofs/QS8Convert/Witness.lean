import Salty.Proofs.QS8Convert.Correct

namespace Salty.Kernels.QS8Convert
open CByte

/-- A nonempty admitted call exercising the repaired -32768² saturation
corner: input zero point 256, raw multiplier 32768, output zero point zero.
The input byte is zero, output is at 32, parameters occupy aligned bytes48--59. -/
def witnessCall : Call := ⟨1, 16#64, 32#64, 48#64, 256, 32768, 0⟩
def witnessState : State :=
  ⟨fun name =>
    if name = "batch" then some (.integer 1)
    else if name = "input" then some (.pointer 16#64)
    else if name = "output" then some (.pointer 32#64)
    else if name = "params" then some (.pointer 48#64)
    else none,
    ⟨fun a => if a = 49#64 then 1 else if a = 53#64 then 128 else 0,
      fun _ => true, fun _ => true⟩⟩

private theorem disjoint_witness (base : Address) (h : base = 16#64 ∨ base = 48#64) :
    ∀ a, Footprint base (if base = 16#64 then 8 else 12) a → ¬ Footprint (32#64) 1 a := by
  intro a ⟨i, hi, hai⟩ ⟨j, hj, haj⟩
  have hj0 : j = 0 := by omega
  subst j
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at haj
  rw [hai] at haj
  have hn := congrArg BitVec.toNat haj
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

theorem witness_saturation : QuantizedISA.neonLane witnessCall.values 0 = 127 := by decide

end Salty.Kernels.QS8Convert
