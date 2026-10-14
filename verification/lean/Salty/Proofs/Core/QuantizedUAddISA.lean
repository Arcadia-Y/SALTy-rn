import Salty.Spec.QU8AddLane
import Salty.Proofs.Core.QuantizedAddISA

/-! Independent unsigned-byte addition lane calculations. These lemmas are
supporting instruction results, not a whole-kernel equivalence theorem. -/
namespace Salty.QuantizedUAddISA
open SIMD.Unsigned
open QuantizedISA
open SIMD.Signed
open SIMD.Arithmetic (extend16 multiply32 neonMla32 rvvMacc32 neonNarrow16 rvvClip16RDN0)

theorem sub_wide_eq (x zero : BitVec 8) : neonSubWide x zero = rvvSubWide x zero := by
  simp [neonSubWide, rvvSubWide, Int.sub_eq_add_neg, BitVec.ofInt_add,
    BitVec.ofInt_neg, BitVec.sub_eq_add_neg, BitVec.zeroExtend_eq_setWidth]

theorem narrow_unsigned_eq (x : BitVec 16) : neonNarrowU8 x = rvvNarrowU8 x := by
  by_cases neg : x.toInt < 0
  · simp [neonNarrowU8, IntegerOps.narrowUnsigned, IntegerOps.saturateUnsigned, rvvNarrowU8, rvvNonnegative16, neg, Int.max_def, Int.min_def,
      show ¬ (0 : Int) ≤ x.toInt by omega]
  · have positive : 0 ≤ x.toInt := by omega
    have rep : x.toInt = (x.toNat : Int) := by
      rw [BitVec.toInt_eq_toNat_cond]
      split
      · rfl
      · have bound := BitVec.isLt x
        have relation := BitVec.toInt_eq_toNat_cond x
        split at relation <;> omega
    unfold neonNarrowU8 IntegerOps.narrowUnsigned IntegerOps.saturateUnsigned rvvNarrowU8 rvvNonnegative16
    rw [if_neg neg, show max (0 : Int) x.toInt = x.toInt from Int.max_eq_right positive, rep]
    by_cases small : x.toNat ≤ 255
    · rw [Nat.min_eq_right small, Int.min_eq_right (by omega)]
      rfl
    · rw [Nat.min_eq_left (by omega), Int.min_eq_left (by omega)]
      rfl

theorem addition_lane_eq (p : Params) (a b : BitVec 8) : neonLane p a b = rvvLane p a b := by
  simp only [neonLane, rvvLane, sub_wide_eq, neonMla32, rvvMacc32,
    BitVec.mul_comm, ShiftISA.shift_eq, neonNarrow16, rvvClip16RDN0, narrow_unsigned_eq]

/-- The unsigned output preserves the same shift32 counterexample. -/
theorem shift32_witness : neonLane ⟨0,0,1,0,32,0,0,255⟩ 1 0 = 0 := by decide

end Salty.QuantizedUAddISA
