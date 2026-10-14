import Salty.Model.SIMD
import Salty.Spec.QuantizedShift

namespace Salty.Rounding
/-- RVV widening multiply followed by VNCLIP with RNU and shift 15.
The 16x16 product fits in a signed 32-bit lane. -/
def wideningClip15 (a b : BitVec 16) : Int :=
  sat16 ((a.toInt * b.toInt + 16384) / 32768)

end Salty.Rounding

/-! Parameter and composed lane definitions for this kernel family. -/
namespace Salty.QuantizedISA
open SIMD.Signed

structure Params where
  inputZero : BitVec 16
  multiplier : BitVec 16
  outputZero : BitVec 16

def neonLane (p : Params) (x : BitVec 8) : BitVec 8 :=
  narrowSat8 (addSat16 (sqrdmulh16 (shift16 (subWide8 p.inputZero x) 7)
    p.multiplier) p.outputZero)

def rvvLane (p : Params) (x : BitVec 8) : BitVec 8 :=
  clipRDN0 (addSat16 (clipRNU15 (wideningMul16
    (shift16 (reverseSub16 (signExtend8 x) p.inputZero) 7) p.multiplier)) p.outputZero)

end Salty.QuantizedISA
