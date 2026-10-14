import Salty.Proofs.QS8Add.Correct
import Salty.Examples.QS8Add

namespace Salty.Kernels.QS8Add
open CByte QuantizedAddISA
open SIMD.Arithmetic

/-- A nonempty admitted caller is the concrete repaired shift-32 counterexample.
The raw parameter, input bytes and scalar multiplier are actual memory bytes. -/
def witnessCall : Call := ⟨1, 16#64, 32#64, 48#64, 64#64,
  ⟨0, 0, 1, 0, 32, 0, 128, 127⟩⟩
def witnessState : State := QS8AddExamples.state 32

private theorem disjoint_input (base : Address) (h : base = 16#64 ∨ base = 32#64) :
    ∀ a, Footprint base 8 a → ¬ Footprint (48#64) 1 a := by
  intro a ⟨i, hi, hai⟩ ⟨j, hj, haj⟩
  have hn := congrArg BitVec.toNat (hai.symm.trans haj)
  rcases h with rfl | rfl <;> simp [BitVec.toNat_add, BitVec.toNat_ofNat] at hn <;> omega

private theorem disjoint_params :
    ∀ a, Footprint (64#64) 24 a → ¬ Footprint (48#64) 1 a := by
  intro a ⟨i, hi, hai⟩ ⟨j, hj, haj⟩
  have hn := congrArg BitVec.toNat (hai.symm.trans haj)
  simp [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
  omega

theorem entry_nonempty : Entry witnessState witnessCall := by
  constructor
  all_goals try { rfl }
  all_goals try { decide }
  · constructor
    · intro a ha; rfl
    · intro a ha; rfl
    · intro a ha; rfl
    · exact disjoint_input _ (Or.inl rfl)
    · exact disjoint_input _ (Or.inr rfl)
  · intro a ha; rfl
  · exact disjoint_params

/-- The old unconditional VSSRA count mask preserves one at raw shift32;
the actual source and repaired target instead write zero. -/
theorem witness_source_zero : neonLane witnessCall.values 1 0 = 0 := by decide
theorem witness_old_shift_one : ShiftISA.rvvRight (1#32) 32 = 1 := by decide

/-- Source and target preserve wrapping left shift when the signed low byte
of the negated raw count is positive (raw255 decodes to +1). -/
theorem witness_left_shift : neonLane { witnessCall.values with shift := 255 } 1 0 = 2 := by decide

theorem witness_result : (resultMemory witnessState witnessCall).data 48#64 = 0 := by decide

end Salty.Kernels.QS8Add
