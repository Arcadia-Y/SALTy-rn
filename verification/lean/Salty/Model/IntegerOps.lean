import Std

/-! Width-parameterized integer operations shared by SIMD instruction adapters.
These are lane operations, without kernel parameters, algorithms or memory layout.
Shift amounts here are effective counts; instruction adapters enforce architectural
count decoding and the supported rounding modes. Width-zero bitvectors remain
mathematically total but are not admitted architectural lanes. -/
namespace Salty.IntegerOps

inductive RoundingMode where
  | nearestUp
  | down
  deriving DecidableEq, Repr

def saturateSigned (width : Nat) (x : Int) : Int :=
  max (-(2 ^ (width - 1))) (min (2 ^ (width - 1) - 1) x)

def saturateUnsigned (width : Nat) (x : Int) : Int :=
  min (2 ^ width - 1) (max 0 x)

def roundShift (mode : RoundingMode) (shift : Nat) (x : Int) : Int :=
  match mode with
  | .nearestUp => if shift = 0 then x else (x + 2 ^ (shift - 1)) / 2 ^ shift
  | .down => x / 2 ^ shift

def narrowSigned (width : Nat) (x : BitVec sourceWidth) : BitVec width :=
  BitVec.ofInt width (saturateSigned width x.toInt)

def narrowUnsigned (width : Nat) (x : BitVec sourceWidth) : BitVec width :=
  BitVec.ofInt width (saturateUnsigned width x.toInt)

def clipSigned (width : Nat) (mode : RoundingMode) (shift : Nat)
    (x : BitVec sourceWidth) : BitVec width :=
  BitVec.ofInt width (saturateSigned width (roundShift mode shift x.toInt))

def addSignedSaturating (x y : BitVec width) : BitVec width :=
  BitVec.ofInt width (saturateSigned width (x.toInt + y.toInt))

def extendSigned (width : Nat) (x : BitVec sourceWidth) : BitVec width :=
  BitVec.ofInt width x.toInt

def multiplySigned (width : Nat) (x : BitVec leftWidth) (y : BitVec rightWidth) : BitVec width :=
  BitVec.ofInt width (x.toInt * y.toInt)

def bitSelect (mask yes no : BitVec width) : BitVec width :=
  (mask &&& yes) ||| (~~~mask &&& no)

def merge (no yes : BitVec width) (mask : Bool) : BitVec width := if mask then yes else no

end Salty.IntegerOps
