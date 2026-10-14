import Salty.Spec.Rsum
import Salty.Proofs.Rsum.Correct
import Salty.Proofs.Rsum.Witness
import Salty.Proofs.Core.TotalCorrect

/-! Final guarantees for Rsum. Read the caller contract and reference result
in `Salty.Spec.Rsum`; implementation lemmas are confined to `Salty.Proofs`.
The generated programs are independently extracted complete source/target bodies.
-/
namespace Salty.Kernels.Rsum
open CByte ReductionISA

/-- Whole-function outcome equivalence for every admitted caller and progressing
bounded vector-length schedule. The observation is the entire memory. -/
theorem behavior_equivalent (cfg : Config) (kind : Interpretation) (c : Call) (capacity : 8 ≤ cfg.capacity) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[(match kind with | .signed => Generated.QS8Rsum.neon | .unsigned => Generated.QU8Rsum.neon)],s⟩)
      (fun s => ⟨[(match kind with | .signed => Generated.QS8Rsum.rvv | .unsigned => Generated.QU8Rsum.rvv)],s⟩) (fun s => Entry kind s c) :=
  behavior_equivalent_proof cfg kind c capacity

/-- The NEON function terminates with the exact reference memory. -/
theorem neon_returns (cfg : Config) (kind : Interpretation) (c : Call) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[(match kind with | .signed => Generated.QS8Rsum.neon | .unsigned => Generated.QU8Rsum.neon)],s⟩) (fun s => Entry kind s c)
      (fun s => resultMemory kind s.memory c) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => neon_correct cfg kind s c h)

/-- The RVV function terminates with the exact reference memory. -/
theorem rvv_returns (cfg : Config) (kind : Interpretation) (c : Call) (capacity : 8 ≤ cfg.capacity) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[(match kind with | .signed => Generated.QS8Rsum.rvv | .unsigned => Generated.QU8Rsum.rvv)],s⟩) (fun s => Entry kind s c)
      (fun s => resultMemory kind s.memory c) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => rvv_correct cfg kind s c h capacity)

/-- The caller domain is inhabited; the result is not vacuous. -/
theorem caller_exists (kind : Interpretation) : ∃ s c, Entry kind s c :=
  ⟨witnessState,witnessCall,entry_nonempty kind⟩

end Salty.Kernels.Rsum

namespace Salty.Kernels.QS8Rsum
open CByte Rsum

theorem behavior_equivalent (cfg : Config) (c : Call) (capacity : 8 ≤ cfg.capacity) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QS8Rsum.neon],s⟩)
      (fun s => ⟨[Generated.QS8Rsum.rvv],s⟩) (fun s => Entry .signed s c) :=
  Rsum.behavior_equivalent cfg .signed c capacity

end Salty.Kernels.QS8Rsum

namespace Salty.Kernels.QU8Rsum
open CByte Rsum

theorem behavior_equivalent (cfg : Config) (c : Call) (capacity : 8 ≤ cfg.capacity) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QU8Rsum.neon],s⟩)
      (fun s => ⟨[Generated.QU8Rsum.rvv],s⟩) (fun s => Entry .unsigned s c) :=
  Rsum.behavior_equivalent cfg .unsigned c capacity

end Salty.Kernels.QU8Rsum
