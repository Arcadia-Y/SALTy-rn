import Salty.Model.NaN

/-! Target merge sequence used by the floating-point repair. No whole-kernel
equivalence is claimed here. -/
namespace Salty.NaN
/-- Four masked integer merges, in the order used by the repaired targets. -/
def repair (a b result : Word) : Word :=
  let result := if isNaN b then quiet b else result
  let result := if isNaN a then quiet a else result
  let result := if isSignaling b then quiet b else result
  if isSignaling a then quiet a else result

end Salty.NaN
