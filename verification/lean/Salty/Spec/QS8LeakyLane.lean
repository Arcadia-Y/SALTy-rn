import Salty.Model.SIMD
import Salty.Spec.QuantizedShift

/-! Parameter and composed lane definitions for this kernel family. -/
namespace Salty.QuantizedLeakyISA
open SIMD.Signed SIMD.Selection

structure Params where
  inputZero : BitVec 16
  positive : BitVec 16
  negative : BitVec 16
  outputZero : BitVec 16

def neonLane (p : Params) (x : BitVec 8) : BitVec 8 :=
  let acc := subWide8 p.inputZero x
  let mask := signedLessMask acc 0
  let multiplier := bitSelect mask p.positive p.negative
  narrowSat8 (addSat16 (sqrdmulh16 (shift16 acc 7) multiplier) p.outputZero)

def rvvLane (p : Params) (x : BitVec 8) : BitVec 8 :=
  let acc := reverseSub16 (signExtend8 x) p.inputZero
  let mask := signedLess acc 0
  let multiplier := merge p.negative p.positive mask
  clipRDN0 (addSat16 (clipRNU15 (wideningMul16 (shift16 acc 7) multiplier)) p.outputZero)

end Salty.QuantizedLeakyISA
