import Salty.Spec.Rsum
import Salty.Proofs.Core.CByteMemory
import Salty.Proofs.Core.ReductionISA

namespace Salty.Kernels.Rsum
open CByte ReductionISA

theorem outputScalar_signed_bounds (initial contribution : BitVec 32)
    (defined : OutputDefined .signed initial contribution) :
    -(2^31) ≤ outputScalar .signed initial contribution ∧ outputScalar .signed initial contribution < 2^31 :=
  defined

theorem outputScalar_unsigned_bounds (initial contribution : BitVec 32) :
    0 ≤ outputScalar .unsigned initial contribution ∧ outputScalar .unsigned initial contribution < 2^32 := by
  have hi := BitVec.isLt (BitVec.ofInt 32 ((initial.toNat : Int) + contribution.toNat))
  simp only [outputScalar]
  constructor <;> omega

theorem resultMemory_frame (kind : Interpretation) (m : Memory) (c : Call) (a : Address)
    (outside : ¬ Footprint c.output 4 a) : (resultMemory kind m c).data a = m.data a := by
  apply writeBytes_frame
  simpa [bytes32] using outside

end Salty.Kernels.Rsum
