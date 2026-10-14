import Std

namespace Salty.ShiftISA

/-- Rounding bit for a nonzero arithmetic right shift. -/
def roundBit (x : BitVec 32) (n : Nat) : BitVec 32 :=
  if x.getLsbD (n - 1) then 1 else 0

/-- SRSHL's signed right-shift branch, with counts clamped to the lane width.
Beyond the width a rounded signed result is zero, as at exactly the width. -/
def neonRight (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x.sshiftRight (min n 32)) + roundBit x (min n 32)

def neonSRSHL (x : BitVec 32) (shiftLane : BitVec 32) : BitVec 32 :=
  let count := (shiftLane.setWidth 8).toInt
  if 0 ≤ count then x <<< count.toNat
  else neonRight x (-count).toNat

/-- VSSRA with RNU uses only the low five count bits. -/
def rvvRight (x : BitVec 32) (n : Nat) : BitVec 32 :=
  let k := n % 32
  x.sshiftRight k + if k = 0 then 0 else roundBit x k

/-- VSLL also masks the count to five bits. -/
def rvvLeft (x : BitVec 32) (n : Nat) : BitVec 32 := x <<< (n % 32)

end Salty.ShiftISA
