import Salty.Generated.QS8AddNeon
import Salty.Generated.QS8AddRvv

/-! Finite executable checks of the actual extracted programs. These are
regressions for the extraction/semantics, not unbounded kernel equivalence. -/
namespace Salty.Kernels.QS8AddExamples
open CByte

def config : Config :=
  ⟨32, fun n => min n 32, by intro n hn; dsimp; omega, by intro n; exact Nat.le_refl _⟩

def state (shift : Byte) : State :=
  ⟨fun name =>
    if name = "batch" then some (.integer 1)
    else if name = "input_a" then some (.pointer 16#64)
    else if name = "input_b" then some (.pointer 32#64)
    else if name = "output" then some (.pointer 48#64)
    else if name = "params" then some (.pointer 64#64)
    else none,
    ⟨fun a => if a = 16#64 ∨ a = 72#64 then 1
      else if a = 80#64 then shift
      else if a = 86#64 then 128 else if a = 87#64 then 127 else 0,
      fun _ => true, fun _ => true⟩⟩

def output (code : Stmt) (shift : Byte) : Option Byte :=
  (run config 128 code (state shift)).map (fun s => s.memory.data 48#64)

-- Compiled finite regressions are run separately by Regression.lean. They are
-- not theorem evidence and are not included in the whole-kernel coverage count.
end Salty.Kernels.QS8AddExamples
