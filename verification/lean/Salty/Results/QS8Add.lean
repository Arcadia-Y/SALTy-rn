import Salty.Spec.QS8Add
import Salty.Proofs.QS8Add.Correct
import Salty.Proofs.QS8Add.Witness
import Salty.Proofs.Core.TotalCorrect

/-! Final guarantees for QS8Add. Read the caller contract and reference result
in `Salty.Spec.QS8Add`; implementation lemmas are confined to `Salty.Proofs`.
The generated programs are independently extracted complete source/target bodies.
-/
namespace Salty.Kernels.QS8Add
open CByte ReductionISA

/-- Whole-function outcome equivalence for every admitted caller and progressing
bounded vector-length schedule. The observation is the entire memory. -/
theorem behavior_equivalent (cfg : Config) (c : Call) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QS8Add.neon],s⟩)
      (fun s => ⟨[Generated.QS8Add.rvv],s⟩) (fun s => Entry s c) :=
  behavior_equivalent_proof cfg c

/-- The NEON function terminates with the exact reference memory. -/
theorem neon_returns (cfg : Config) (c : Call) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[Generated.QS8Add.neon],s⟩) (fun s => Entry s c)
      (fun s => resultMemory s c) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => neon_correct cfg s c h)

/-- The RVV function terminates with the exact reference memory. -/
theorem rvv_returns (cfg : Config) (c : Call) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[Generated.QS8Add.rvv],s⟩) (fun s => Entry s c)
      (fun s => resultMemory s c) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => rvv_correct cfg s c h)

/-- The caller domain is inhabited; the result is not vacuous. -/
theorem caller_exists : ∃ s c, Entry s c :=
  ⟨witnessState,witnessCall,entry_nonempty⟩

end Salty.Kernels.QS8Add
