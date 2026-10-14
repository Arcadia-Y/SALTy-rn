import Salty.Spec.Rdsum
import Salty.Proofs.Core.CRowSum
import Salty.Proofs.Core.RowSumVectors

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

@[simp] theorem outputWords_length (kind : Interpretation) (m : Memory) (c : Call) :
    (outputWords kind m c).length = c.channels := by simp [outputWords]

@[simp] theorem resultMemory_readable (kind : Interpretation) (m : Memory) (c : Call) :
    (resultMemory kind m c).readable = m.readable := by simp [resultMemory]

@[simp] theorem resultMemory_writable (kind : Interpretation) (m : Memory) (c : Call) :
    (resultMemory kind m c).writable = m.writable := by simp [resultMemory]

theorem resultMemory_frame (kind : Interpretation) (m : Memory) (c : Call) (a : Address)
    (outside : ¬ Footprint c.output (4*c.channels) a) :
    (resultMemory kind m c).data a = m.data a := by
  apply writeBytes_frame
  simpa using outside

end Salty.Kernels.Rdsum
