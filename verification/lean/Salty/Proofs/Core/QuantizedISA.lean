import Salty.Spec.QS8ConvertLane
import Salty.Proofs.Core.Rounding

/-! Lane semantics for the integer conversion instructions used by qs8-vcvt.
Each instruction retains its own lane width, wrapping, rounding and saturation.
The lane theorem is infrastructure; it is not a whole-kernel proof. -/
namespace Salty.QuantizedISA
open SIMD.Signed

theorem wideningMul16_exact (a b : BitVec 16) :
    (wideningMul16 a b).toInt = a.toInt * b.toInt := by
  have lo := BitVec.le_toInt_mul_toInt (x := a) (y := b)
  have hi := BitVec.toInt_mul_toInt_le (x := a) (y := b)
  apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega

theorem subWide8_eq (zero : BitVec 16) (x : BitVec 8) :
    subWide8 zero x = reverseSub16 (signExtend8 x) zero := by
  simp [subWide8, reverseSub16, signExtend8, IntegerOps.extendSigned, Int.sub_eq_add_neg,
    BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem multiply_eq (a b : BitVec 16) :
    sqrdmulh16 a b = clipRNU15 (wideningMul16 a b) := by
  change BitVec.ofInt 16 (Rounding.sqrdmulh16 a b) =
    BitVec.ofInt 16 (Rounding.sat16 (((wideningMul16 a b).toInt + 16384) / 32768))
  rw [wideningMul16_exact, Rounding.sqrdmulh16_eq_clip15]
  rfl

/-- All byte inputs and all narrowed parameter bit patterns, including the
positive saturation corner repaired in the target. -/
theorem conversion_lane_eq (p : Params) (x : BitVec 8) : neonLane p x = rvvLane p x := by
  simp only [neonLane, rvvLane, subWide8_eq, multiply_eq, narrowSat8, clipRDN0]

end Salty.QuantizedISA
