import Salty.Generated.QS8RsumNeon
import Salty.Generated.QS8RsumRvv
import Salty.Generated.QU8RsumNeon
import Salty.Generated.QU8RsumRvv

/-! Finite compiled executions of the extracted reduction programs. These
exercise the new bridge; they are not unbounded correctness theorems. -/
namespace Salty.Kernels.RsumExamples
open CByte

def config (capacity : Nat) (positive : 0 < capacity) (balanced : Bool) : Config where
  capacity := capacity
  choose := fun n => if balanced ∧ capacity < n ∧ n < 2 * capacity then (n + 1) / 2 else min n capacity
  positive := by
    intro n hn
    split <;> omega
  bounded := by
    intro n
    split <;> omega

def state (n : Nat) (byte : Byte) (initial : Int) : State :=
  ⟨fun name =>
    if name = "batch" then some (.integer n)
    else if name = "input" then some (.pointer 4096#64)
    else if name = "output" then some (.pointer 16#64)
    else if name = "params" then some (.pointer 32#64)
    else none,
   ⟨fun a => if 16 ≤ a.toNat ∧ a.toNat < 20 then
      (bytes32 initial)[a.toNat - 16]!
    else if 4096 ≤ a.toNat ∧ a.toNat < 4096 + n then byte
    else 213,
    fun a => (16 ≤ a.toNat ∧ a.toNat < 20) ∨ (4096 ≤ a.toNat ∧ a.toNat < 4096 + n + 15),
    fun a => 16 ≤ a.toNat ∧ a.toNat < 20⟩⟩

def output (cfg : Config) (code : Stmt) (n : Nat) (byte : Byte) (initial : Int) : Option (List Byte) :=
  (run cfg 1024 code (state n byte initial)).map (fun s =>
    [s.memory.data 16#64, s.memory.data 17#64, s.memory.data 18#64, s.memory.data 19#64])

end Salty.Kernels.RsumExamples
