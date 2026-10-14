import Std

/-! Review-facing definitions. Supporting lemmas live in `Salty.Proofs.Core.Rounding`. -/

namespace Salty.Rounding

def sat16 (x : Int) : Int := max (-32768) (min 32767 x)

/-- ARM SQRDMULH's signed 16-bit lane result, with the doubling evaluated
in mathematical integers before rounding and saturation. -/
def sqrdmulh16 (a b : BitVec 16) : Int :=
  sat16 ((2 * (a.toInt * b.toInt) + 32768) / 65536)

end Salty.Rounding
