import Salty.Model.SIMD
import Salty.Spec.QuantizedShift
import Salty.Spec.QS8AddLane

/-! Parameter and composed lane definitions for this kernel family. -/
namespace Salty.QuantizedUAddISA
open SIMD.Signed SIMD.Unsigned
open SIMD.Arithmetic (extend16 multiply32 neonMla32 rvvMacc32 neonNarrow16 rvvClip16RDN0)
abbrev Params := QuantizedAddISA.Params

/-- Reinterpret the nonnegative signed lane as unsigned16, then VNCLIPU at0. -/
def rvvNarrowU8 (x : BitVec 16) : BitVec 8 :=
  BitVec.ofNat 8 (min 255 (rvvNonnegative16 x).toNat)
def neonLane (p : Params) (a b : BitVec 8) : BitVec 8 :=
  let a32 := extend16 (neonSubWide a p.aZero)
  let b32 := extend16 (neonSubWide b p.bZero)
  let acc := neonMla32 (multiply32 a32 p.aMultiplier) b32 p.bMultiplier
  let shifted := ShiftISA.neonShift acc p.shift
  let out := neonNarrowU8 (addSat16 (neonNarrow16 shifted) p.outputZero)
  min8 (max8 out p.outputMin) p.outputMax

def rvvLane (p : Params) (a b : BitVec 8) : BitVec 8 :=
  let a32 := extend16 (rvvSubWide a p.aZero)
  let b32 := extend16 (rvvSubWide b p.bZero)
  let acc := rvvMacc32 (multiply32 a32 p.aMultiplier) p.bMultiplier b32
  let shifted := ShiftISA.repairedShift acc p.shift
  let out := rvvNarrowU8 (addSat16 (rvvClip16RDN0 shifted) p.outputZero)
  min8 (max8 out p.outputMin) p.outputMax

end Salty.QuantizedUAddISA
