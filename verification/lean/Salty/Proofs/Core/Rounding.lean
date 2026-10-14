import Salty.Spec.QS8ConvertLane
import Std

namespace Salty.Rounding

theorem rounding_identity (p : Int) :
    (2 * p + 32768) / 65536 = (p + 16384) / 32768 := by omega

/-- Unconditional over all input lane bit patterns, including -32768². -/
theorem sqrdmulh16_eq_clip15 (a b : BitVec 16) :
    sqrdmulh16 a b = wideningClip15 a b := by
  unfold sqrdmulh16 wideningClip15
  rw [rounding_identity]

theorem saturation_corner :
    wideningClip15 (BitVec.ofInt 16 (-32768)) (BitVec.ofInt 16 (-32768)) = 32767 := by
  decide

end Salty.Rounding
