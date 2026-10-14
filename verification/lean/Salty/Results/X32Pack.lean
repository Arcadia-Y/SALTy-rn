import Salty.Spec.X32Pack
import Salty.Proofs.X32Pack.Correct
import Salty.Proofs.X32Pack.Witness
import Salty.Proofs.Core.TotalCorrect

/-! Final guarantees for X32Pack. Read the caller contract and reference result
in `Salty.Spec.X32Pack`; implementation lemmas are confined to `Salty.Proofs`.
The generated programs are independently extracted complete source/target bodies.
-/
namespace Salty.Kernels.X32Pack
open CByte ReductionISA

/-- Whole-function outcome equivalence for every admitted caller and progressing
bounded vector-length schedule. The observation is the entire memory. -/
theorem behavior_equivalent (cfg : Config) (c : Call) (capacity : 8 ≤ cfg.capacity) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.X32Pack.neon],s⟩)
      (fun s => ⟨[Generated.X32Pack.rvv],s⟩) (fun s => Entry s c) :=
  behavior_equivalent_proof cfg c capacity

/-- The NEON function terminates with the exact reference memory. -/
theorem neon_returns (cfg : Config) (c : Call) (capacity : 8 ≤ cfg.capacity) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[Generated.X32Pack.neon],s⟩) (fun s => Entry s c)
      (fun s => packGroups c.channels c.depth c.extra c.groups s.memory c.weights c.bias c.output) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => correct false cfg capacity s c h)

/-- The RVV function terminates with the exact reference memory. -/
theorem rvv_returns (cfg : Config) (c : Call) (capacity : 8 ≤ cfg.capacity) :
    Salty.TotalCorrect (CByte.machine cfg)
      (fun s => ⟨[Generated.X32Pack.rvv],s⟩) (fun s => Entry s c)
      (fun s => packGroups c.channels c.depth c.extra c.groups s.memory c.weights c.bias c.output) :=
  CByte.totalCorrect_of_exec _ _ _ _ (fun s h => correct true cfg capacity s c h)

/-- The caller domain is inhabited; the result is not vacuous. -/
theorem caller_exists (withBias : Bool) : ∃ s c, Entry s c :=
  ⟨witnessState withBias,witnessCall withBias,entry_nonempty withBias⟩

end Salty.Kernels.X32Pack
