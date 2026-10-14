import Salty.Spec.X32Transpose
import Salty.Proofs.X32Transpose.Correct
import Salty.Proofs.X32Transpose.Witness
import Salty.Proofs.Core.TotalCorrect

/-! Final guarantees for X32Transpose. Read the caller contract and reference result
in `Salty.Spec.X32Transpose`; implementation lemmas are confined to `Salty.Proofs`.
The generated programs are independently extracted complete source/target bodies.
-/
namespace Salty.Kernels.X32Transpose
open CByte ReductionISA

/-- Whole-function outcome equivalence for every admitted caller and progressing
bounded vector-length schedule. The observation is the entire memory. -/
theorem behavior_equivalent (cfg : Config) (p : MatrixCopy) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.X32Transpose.neon],s⟩)
      (fun s => ⟨[Generated.X32Transpose.rvv],s⟩) (fun s => Entry s p) :=
  behavior_equivalent_proof cfg p

/-- The NEON function terminates with the exact reference memory. -/
theorem neon_returns (cfg : Config) (p : MatrixCopy) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[Generated.X32Transpose.neon],s⟩) (fun s => Entry s p)
      (fun s => (effectiveMatrix p).result s.memory) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => neon_function_total cfg s p h.arguments h.rows h.outputAssertion h.inputAssertion h.source_safe h.source_separated)

/-- The RVV function terminates with the exact reference memory. -/
theorem rvv_returns (cfg : Config) (p : MatrixCopy) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[Generated.X32Transpose.rvv],s⟩) (fun s => Entry s p)
      (fun s => (effectiveMatrix p).result s.memory) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => rvv_function_total cfg s p h.arguments h.rows h.cols h.outputAssertion h.inputAssertion h.effective_safe.common h.effective_separated)

/-- The caller domain is inhabited; the result is not vacuous. -/
theorem caller_exists : ∃ s p, Entry s p :=
  ⟨witnessState,witnessMatrix,entry_nonempty⟩

end Salty.Kernels.X32Transpose
