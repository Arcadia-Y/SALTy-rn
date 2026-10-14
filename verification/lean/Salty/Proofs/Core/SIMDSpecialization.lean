import Salty.Model.SIMD

/-! The shared operations agree with the pre-refactor fixed-width arithmetic
formulas for every operand, not just the finite regression inputs. The actual
SIMD adapters now delegate to these shared operations. -/
namespace Salty.SIMD

theorem clip_rnu15_specialization (x : BitVec 32) :
    Signed.clipRNU15 x = BitVec.ofInt 16 (Rounding.sat16 ((x.toInt + 16384) / 32768)) := by rfl

theorem clip_rdn0_specialization (x : BitVec 16) :
    Signed.clipRDN0 x = BitVec.ofInt 8 (Signed.sat8 x.toInt) := by rfl

theorem narrow_signed_specialization (x : BitVec 16) :
    Signed.narrowSat8 x = BitVec.ofInt 8 (Signed.sat8 x.toInt) := by rfl

theorem narrow_unsigned_specialization (x : BitVec 16) :
    Unsigned.neonNarrowU8 x = BitVec.ofInt 8 (min 255 (max 0 x.toInt)) := by rfl

theorem add_saturating_specialization (x y : BitVec 16) :
    Signed.addSat16 x y = BitVec.ofInt 16 (Rounding.sat16 (x.toInt + y.toInt)) := by rfl

theorem widening_multiply_specialization (x y : BitVec 16) :
    Signed.wideningMul16 x y = BitVec.ofInt 32 (x.toInt * y.toInt) := by rfl

theorem sign_extend_specialization (x : BitVec 8) :
    Signed.signExtend8 x = BitVec.ofInt 16 x.toInt := by rfl

theorem bit_select_specialization (mask yes no : BitVec 16) :
    Selection.bitSelect mask yes no = (mask &&& yes) ||| (~~~mask &&& no) := by rfl

theorem merge_specialization (no yes : BitVec 16) (mask : Bool) :
    Selection.merge no yes mask = (if mask then yes else no) := by rfl

end Salty.SIMD
