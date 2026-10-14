import Salty.Spec.QS8LeakyLane
import Salty.Proofs.Core.QuantizedISA

/-! Independent lane calculations for qs8-vlrelu. This supporting theorem does
not certify a kernel: extraction and whole-loop refinement are still required. -/
namespace Salty.QuantizedLeakyISA
open SIMD.Selection
open QuantizedISA
open SIMD.Signed

theorem bitSelect_compare (a b yes no : BitVec 16) :
    bitSelect (signedLessMask a b) yes no = merge no yes (signedLess a b) := by
  by_cases h : a.toInt < b.toInt
  · simp [signedLessMask, bitSelect, IntegerOps.bitSelect, signedLess, merge, IntegerOps.merge, h]
    exact BitVec.allOnes_and
  · simp [signedLessMask, bitSelect, IntegerOps.bitSelect, signedLess, merge, IntegerOps.merge, h]
    exact BitVec.allOnes_and

/-- Independent instruction-level lane equality, including signed selection
before shifting and every wrapping/saturating corner. -/
theorem leaky_lane_eq (p : Params) (x : BitVec 8) : neonLane p x = rvvLane p x := by
  simp only [neonLane, rvvLane, subWide8_eq, bitSelect_compare, multiply_eq,
    narrowSat8, clipRDN0]

end Salty.QuantizedLeakyISA
