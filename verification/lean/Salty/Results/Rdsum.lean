import Salty.Spec.Rdsum
import Salty.Proofs.Rdsum.Correct
import Salty.Proofs.Rdsum.Witness
import Salty.Proofs.Core.TotalCorrect

/-! Final guarantees for Rdsum. Read the caller contract and reference result
in `Salty.Spec.Rdsum`; implementation lemmas are confined to `Salty.Proofs`.
The generated programs are independently extracted complete source/target bodies.
-/
namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- Whole-function outcome equivalence for every admitted caller and progressing
bounded vector-length schedule. The observation is the entire memory. -/
theorem behavior_equivalent (cfg : Config) (kind : Interpretation) (c : Call) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[(match kind with | .signed => Generated.QS8Rdsum.neon | .unsigned => Generated.QU8Rdsum.neon)],s⟩)
      (fun s => ⟨[(match kind with | .signed => Generated.QS8Rdsum.rvv | .unsigned => Generated.QU8Rdsum.rvv)],s⟩) (fun s => Entry kind s c) :=
  behavior_equivalent_proof cfg kind c

/-- The NEON function terminates with the exact reference memory. -/
theorem neon_returns (cfg : Config) (kind : Interpretation) (c : Call) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[(match kind with | .signed => Generated.QS8Rdsum.neon | .unsigned => Generated.QU8Rdsum.neon)],s⟩) (fun s => Entry kind s c)
      (fun s => resultMemory kind s.memory c) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => neon_correct kind cfg s c h)

/-- The RVV function terminates with the exact reference memory. -/
theorem rvv_returns (cfg : Config) (kind : Interpretation) (c : Call) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[(match kind with | .signed => Generated.QS8Rdsum.rvv | .unsigned => Generated.QU8Rdsum.rvv)],s⟩) (fun s => Entry kind s c)
      (fun s => resultMemory kind s.memory c) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => rvv_correct kind cfg s c h)

/-- The caller domain is inhabited; the result is not vacuous. -/
theorem caller_exists (kind : Interpretation) : ∃ s c, Entry kind s c :=
  ⟨witnessState,witnessCall,entry_nonempty kind⟩

end Salty.Kernels.Rdsum

namespace Salty.Kernels.QS8Rdsum
open CByte Rdsum

theorem behavior_equivalent (cfg : Config) (c : Call) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QS8Rdsum.neon],s⟩)
      (fun s => ⟨[Generated.QS8Rdsum.rvv],s⟩) (fun s => Entry .signed s c) :=
  Rdsum.behavior_equivalent cfg .signed c

end Salty.Kernels.QS8Rdsum

namespace Salty.Kernels.QU8Rdsum
open CByte Rdsum

theorem behavior_equivalent (cfg : Config) (c : Call) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QU8Rdsum.neon],s⟩)
      (fun s => ⟨[Generated.QU8Rdsum.rvv],s⟩) (fun s => Entry .unsigned s c) :=
  Rdsum.behavior_equivalent cfg .unsigned c

end Salty.Kernels.QU8Rdsum
