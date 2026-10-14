import Salty.Model.CByteMemory

namespace Salty.Kernels.S8Clamp.Execution
open CByte

/-- The source may read up to seven bytes beyond the logical input end. Those
bytes belong to the input object and are also separated from the output. -/
structure PaddedSafe (m : Memory) (input output : Address) (n : Nat) : Prop where
  readable : ∀ a, Footprint input (n + 7) a → m.readable a = true
  writable : ∀ a, Footprint output n a → m.writable a = true
  separate : ∀ a, Footprint input (n + 7) a → ¬ Footprint output n a

end Salty.Kernels.S8Clamp.Execution
