import Salty.Spec.NaNRepair
import Std

namespace Salty.NaN

/-- The repair implements the selection policy for every pair of bit patterns
and every original instruction result. This does not assert equality of the
finite arithmetic operations or floating-point exception flags. -/
theorem repair_eq_selection (a b result : Word) :
    repair a b result = (armSelection a b).getD result := by
  simp only [repair, armSelection]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem signaling_is_nan (a : Word) : isSignaling a = true → isNaN a = true := by
  intro h
  simp only [isSignaling, Bool.and_eq_true] at h
  exact h.1

theorem quiet_is_nan (a : Word) (h : isNaN a = true) : isNaN (quiet a) = true := by
  have distrib : (a ||| 0x00400000) &&& 0x7fffffff =
      (a &&& 0x7fffffff) ||| ((0x00400000 : Word) &&& 0x7fffffff) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases (0x00400000 : Word).getLsbD i <;>
      cases (0x7fffffff : Word).getLsbD i <;> decide
  simp only [isNaN, magnitude, quiet, BitVec.ult_iff_toNat_lt] at *
  rw [distrib, BitVec.toNat_or]
  exact Nat.lt_of_lt_of_le h Nat.left_le_or

theorem min_counterexample :
    armSelection 0x7fc00123 0x3f800000 = some 0x7fc00123 := by decide

end Salty.NaN
