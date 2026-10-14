import Salty.Spec.QS8Convert
import Salty.Proofs.QS8Convert.Correct
import Salty.Proofs.QS8Convert.Witness
import Salty.Proofs.Core.TotalCorrect

/-! Final guarantees for QS8Convert. Read the caller contract and reference result
in `Salty.Spec.QS8Convert`; implementation lemmas are confined to `Salty.Proofs`.
The generated programs are independently extracted complete source/target bodies.
-/
namespace Salty.Kernels.QS8Convert
open CByte ReductionISA

/-- Whole-function outcome equivalence for every admitted caller and progressing
bounded vector-length schedule. The observation is the entire memory. -/
theorem behavior_equivalent (cfg : Config) (c : Call) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QS8Convert.neon],s⟩)
      (fun s => ⟨[Generated.QS8Convert.rvv],s⟩) (fun s => Entry s c) :=
  behavior_equivalent_proof cfg c

/-- The NEON function terminates with the exact reference memory. -/
theorem neon_returns (cfg : Config) (c : Call) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[Generated.QS8Convert.neon],s⟩) (fun s => Entry s c)
      (fun s => resultMemory s c) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => neon_correct cfg s c h)

/-- The RVV function terminates with the exact reference memory. -/
theorem rvv_returns (cfg : Config) (c : Call) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[Generated.QS8Convert.rvv],s⟩) (fun s => Entry s c)
      (fun s => resultMemory s c) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => rvv_correct cfg s c h)

/-- The caller domain is inhabited; the result is not vacuous. -/
theorem caller_exists : ∃ s c, Entry s c :=
  ⟨witnessState,witnessCall,entry_nonempty⟩

end Salty.Kernels.QS8Convert
