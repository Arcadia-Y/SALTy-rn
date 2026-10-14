import Salty.Spec.QS8AddLane
import Salty.Proofs.Core.QuantizedISA
import Salty.Proofs.Core.ShiftISA

/-! Per-instruction lane calculations for qs8-vadd-minmax. Multiplication and
accumulation wrap at 32 bits before the signed variable shift. This is supporting
infrastructure, not a theorem about the complete extracted functions. -/
namespace Salty.QuantizedAddISA
open SIMD.Arithmetic
open QuantizedISA
open SIMD.Signed

theorem sub_wide_eq (x zero : BitVec 8) : neonSubWide x zero = rvvSubWide x zero := by
  simp [neonSubWide, rvvSubWide, signExtend8, IntegerOps.extendSigned, Int.sub_eq_add_neg,
    BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- No range restriction on multipliers, zero points or narrowed clamp bounds.
The raw INT32_MIN shift pattern is allowed by lane semantics; defined source C
must separately exclude it because its scalar initializer negates that value. -/
theorem addition_lane_eq (p : Params) (a b : BitVec 8) : neonLane p a b = rvvLane p a b := by
  simp only [neonLane, rvvLane, sub_wide_eq, neonMla32, rvvMacc32,
    BitVec.mul_comm, ShiftISA.shift_eq, neonNarrow16, rvvClip16RDN0,
    narrowSat8, clipRDN0]

end Salty.QuantizedAddISA
