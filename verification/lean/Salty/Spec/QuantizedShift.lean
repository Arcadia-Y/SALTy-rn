import Salty.Model.ShiftISA

/-! Scalar shift-count decoding and composed shifts used by quantized addition. -/
namespace Salty.ShiftISA

/-- SRSHL uses the signed low byte of its second lane. The source builds that
lane by negating the raw shift parameter (which must not be INT32_MIN in C). -/
def neonCount (raw : BitVec 32) : Int := ((-raw).setWidth 8).toInt

/-- The repaired target uses unsigned 32-bit negation, masks to one byte, then
subtracts 256 when that byte's sign bit is set. -/
def rvvCount (raw : BitVec 32) : Int :=
  let low := (-raw).toNat % 256
  (low : Int) - if 128 ≤ low then 256 else 0

def neonShift (x : BitVec 32) (raw : BitVec 32) : BitVec 32 := neonSRSHL x (-raw)

/-- Actual repaired target branch structure, after scalar count decoding. -/
def repairedShift (x : BitVec 32) (raw : BitVec 32) : BitVec 32 :=
  let count := rvvCount raw
  if count ≤ -32 ∨ 32 ≤ count then 0
  else if count < 0 then rvvRight x (-count).toNat
  else rvvLeft x count.toNat

end Salty.ShiftISA
