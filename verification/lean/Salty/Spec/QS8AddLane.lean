import Salty.Model.SIMD
import Salty.Spec.QuantizedShift

/-! Parameter and composed lane definitions for this kernel family. -/
namespace Salty.QuantizedAddISA
open SIMD.Signed SIMD.Arithmetic

structure Params where
  aZero : BitVec 8
  bZero : BitVec 8
  aMultiplier : BitVec 32
  bMultiplier : BitVec 32
  shift : BitVec 32
  outputZero : BitVec 16
  outputMin : BitVec 8
  outputMax : BitVec 8

def neonLane (p : Params) (a b : BitVec 8) : BitVec 8 :=
  let a32 := extend16 (neonSubWide a p.aZero)
  let b32 := extend16 (neonSubWide b p.bZero)
  let acc := neonMla32 (multiply32 a32 p.aMultiplier) b32 p.bMultiplier
  let shifted := ShiftISA.neonShift acc p.shift
  let out := narrowSat8 (addSat16 (neonNarrow16 shifted) p.outputZero)
  min8 (max8 out p.outputMin) p.outputMax

def rvvLane (p : Params) (a b : BitVec 8) : BitVec 8 :=
  let a32 := extend16 (rvvSubWide a p.aZero)
  let b32 := extend16 (rvvSubWide b p.bZero)
  let acc := rvvMacc32 (multiply32 a32 p.aMultiplier) p.bMultiplier b32
  let shifted := ShiftISA.repairedShift acc p.shift
  let out := clipRDN0 (addSat16 (rvvClip16RDN0 shifted) p.outputZero)
  min8 (max8 out p.outputMin) p.outputMax

end Salty.QuantizedAddISA
