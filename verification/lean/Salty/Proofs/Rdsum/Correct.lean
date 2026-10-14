import Salty.Proofs.Rdsum.NeonCorrect
import Salty.Proofs.Core.CByteMachine

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- Both complete extracted functions terminate with exactly the original-memory
scalar result, for every progressing bounded RVV vector-length schedule. -/
theorem extracted_equivalent (cfg : Config) (kind : Interpretation) (c : Call) :
    CByte.Equivalent cfg (neonProgram kind) (rvvProgram kind) (fun s => Entry kind s c) := by
  intro s h
  obtain ⟨a,ha,hma⟩ := neon_correct kind cfg s c h
  obtain ⟨b,hb,hmb⟩ := rvv_correct kind cfg s c h
  exact ⟨a,b,ha,hb,hma.trans hmb.symm⟩

/-- Whole-function return/fault/divergence equivalence under the common caller
contract; returned observations include all bytes and memory permissions. -/
theorem behavior_equivalent_proof (cfg : Config) (kind : Interpretation) (c : Call) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[neonProgram kind],s⟩) (fun s => ⟨[rvvProgram kind],s⟩)
      (fun s => Entry kind s c) := (extracted_equivalent cfg kind c).behavior

end Salty.Kernels.Rdsum

namespace Salty.Kernels.QS8Rdsum
open CByte Rdsum

theorem behavior_equivalent_proof (cfg : Config) (c : Call) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QS8Rdsum.neon],s⟩) (fun s => ⟨[Generated.QS8Rdsum.rvv],s⟩)
      (fun s => Entry .signed s c) := Rdsum.behavior_equivalent_proof cfg .signed c

end Salty.Kernels.QS8Rdsum

namespace Salty.Kernels.QU8Rdsum
open CByte Rdsum

theorem behavior_equivalent_proof (cfg : Config) (c : Call) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QU8Rdsum.neon],s⟩) (fun s => ⟨[Generated.QU8Rdsum.rvv],s⟩)
      (fun s => Entry .unsigned s c) := Rdsum.behavior_equivalent_proof cfg .unsigned c

end Salty.Kernels.QU8Rdsum
