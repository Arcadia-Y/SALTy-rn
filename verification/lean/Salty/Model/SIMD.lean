import Salty.Model.IntegerOps
import Salty.Model.Rounding
import Salty.Model.ShiftISA

/-! Shared integer SIMD operations. Kernel parameters and instruction sequences
live in Spec/*Lane. Lane widths and signedness remain explicit. -/
namespace Salty.SIMD.Signed

def sat8 (n : Int) : Int := max (-128) (min 127 n)
def subWide8 (zero : BitVec 16) (x : BitVec 8) : BitVec 16 :=
  BitVec.ofInt 16 (zero.toInt - x.toInt)
def shift16 (x : BitVec 16) (n : Nat) : BitVec 16 := x <<< n
def sqrdmulh16 (a b : BitVec 16) : BitVec 16 :=
  BitVec.ofInt 16 (Rounding.sqrdmulh16 a b)
def addSat16 (a b : BitVec 16) : BitVec 16 :=
  IntegerOps.addSignedSaturating a b
def narrowSat8 (a : BitVec 16) : BitVec 8 := IntegerOps.narrowSigned 8 a

def signExtend8 (x : BitVec 8) : BitVec 16 := IntegerOps.extendSigned 16 x
def reverseSub16 (x zero : BitVec 16) : BitVec 16 := zero - x
def wideningMul16 (a b : BitVec 16) : BitVec 32 :=
  IntegerOps.multiplySigned 32 a b
/-- VNCLIP.WX, shift 15, RNU: add half a unit before the arithmetic shift,
then saturate to the destination width. The addition does not wrap. -/
def clipRNU15 (a : BitVec 32) : BitVec 16 :=
  IntegerOps.clipSigned 16 .nearestUp 15 a
/-- VNCLIP.WX, shift zero, RDN: no discarded bits; signed saturation only. -/
def clipRDN0 (a : BitVec 16) : BitVec 8 := IntegerOps.narrowSigned 8 a

end Salty.SIMD.Signed

namespace Salty.SIMD.Selection
open Salty.SIMD.Signed

/-- NEON VCLT produces an all-ones or all-zero 16-bit lane. -/
def signedLessMask (a b : BitVec 16) : BitVec 16 :=
  if a.toInt < b.toInt then 65535 else 0

/-- NEON BSL selects individual bits, not an abstract Boolean branch. -/
def bitSelect (mask yes no : BitVec 16) : BitVec 16 :=
  IntegerOps.bitSelect mask yes no

/-- RVV VMSLT/V MERGE use a Boolean per active lane. -/
def signedLess (a b : BitVec 16) : Bool := a.toInt < b.toInt

def merge (no yes : BitVec 16) (mask : Bool) : BitVec 16 := IntegerOps.merge no yes mask

end Salty.SIMD.Selection

namespace Salty.SIMD.Arithmetic
open Salty.SIMD.Signed

def neonSubWide (x zero : BitVec 8) : BitVec 16 :=
  BitVec.ofInt 16 (x.toInt - zero.toInt)
def rvvSubWide (x zero : BitVec 8) : BitVec 16 :=
  signExtend8 x - signExtend8 zero
def extend16 (x : BitVec 16) : BitVec 32 := BitVec.ofInt 32 x.toInt
def multiply32 (x y : BitVec 32) : BitVec 32 := x * y
def neonMla32 (acc x y : BitVec 32) : BitVec 32 := acc + x * y
def rvvMacc32 (acc scalar vector : BitVec 32) : BitVec 32 := acc + scalar * vector
def neonNarrow16 (x : BitVec 32) : BitVec 16 :=
  BitVec.ofInt 16 (Rounding.sat16 x.toInt)
def rvvClip16RDN0 (x : BitVec 32) : BitVec 16 :=
  BitVec.ofInt 16 (Rounding.sat16 x.toInt)
def max8 (x bound : BitVec 8) : BitVec 8 := if x.toInt < bound.toInt then bound else x
def min8 (x bound : BitVec 8) : BitVec 8 := if bound.toInt < x.toInt then bound else x

end Salty.SIMD.Arithmetic

namespace Salty.SIMD.Unsigned
open Salty.SIMD.Signed

/-- NEON VSUBL_U8 followed by reinterpretation as signed16; negative differences
retain their two's-complement representation and are then sign-extended. -/
def neonSubWide (x zero : BitVec 8) : BitVec 16 :=
  BitVec.ofInt 16 ((x.toNat : Int) - zero.toNat)
def rvvSubWide (x zero : BitVec 8) : BitVec 16 :=
  x.zeroExtend 16 - zero.zeroExtend 16

def neonNarrowU8 (x : BitVec 16) : BitVec 8 :=
  IntegerOps.narrowUnsigned 8 x
def rvvNonnegative16 (x : BitVec 16) : BitVec 16 :=
  if x.toInt < 0 then 0 else x
def max8 (x bound : BitVec 8) : BitVec 8 := if x.toNat < bound.toNat then bound else x
def min8 (x bound : BitVec 8) : BitVec 8 := if bound.toNat < x.toNat then bound else x

end Salty.SIMD.Unsigned
