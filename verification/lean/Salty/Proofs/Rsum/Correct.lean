import Salty.Proofs.Rsum.NeonComplete
import Salty.Proofs.Core.CByteMachine

namespace Salty.Kernels.Rsum
open CByte ReductionISA

/-- Independent source and target executions reach the same memory, including
permissions and bytes outside the four-byte scalar output. -/
theorem extracted_equivalent (cfg : Config) (kind : Interpretation) (c : Call)
    (capacity : 8 ≤ cfg.capacity) :
    CByte.Equivalent cfg (neonProgram kind) (rvvProgram kind) (fun s => Entry kind s c) := by
  intro s h
  obtain ⟨a, ha, hma⟩ := neon_correct cfg kind s c h
  obtain ⟨b, hb, hmb⟩ := rvv_correct cfg kind s c h capacity
  exact ⟨a, b, ha, hb, hma.trans hmb.symm⟩

/-- Whole-function return/fault/divergence equivalence under the common caller
contract, for every bounded progressing vector-length schedule. -/
theorem behavior_equivalent_proof (cfg : Config) (kind : Interpretation) (c : Call)
    (capacity : 8 ≤ cfg.capacity) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[neonProgram kind], s⟩)
      (fun s => ⟨[rvvProgram kind], s⟩) (fun s => Entry kind s c) :=
  (extracted_equivalent cfg kind c capacity).behavior

end Salty.Kernels.Rsum

namespace Salty.Kernels.QS8Rsum
open CByte Rsum

theorem behavior_equivalent_proof (cfg : Config) (c : Call) (capacity : 8 ≤ cfg.capacity) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QS8Rsum.neon], s⟩)
      (fun s => ⟨[Generated.QS8Rsum.rvv], s⟩) (fun s => Entry .signed s c) :=
  Rsum.behavior_equivalent_proof cfg .signed c capacity

end Salty.Kernels.QS8Rsum

namespace Salty.Kernels.QU8Rsum
open CByte Rsum

theorem behavior_equivalent_proof (cfg : Config) (c : Call) (capacity : 8 ≤ cfg.capacity) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QU8Rsum.neon], s⟩)
      (fun s => ⟨[Generated.QU8Rsum.rvv], s⟩) (fun s => Entry .unsigned s c) :=
  Rsum.behavior_equivalent_proof cfg .unsigned c capacity

end Salty.Kernels.QU8Rsum
