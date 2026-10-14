import Salty.Examples.Rsum
import Salty.Proofs.Core.CByteMemory
import Salty.Generated.QS8RdsumNeon
import Salty.Generated.QS8RdsumRvv
import Salty.Generated.QU8RdsumNeon
import Salty.Generated.QU8RdsumRvv

/-! Executable examples only. The oracle sums scalar bytes directly and does
not call the row-sum reference specification or instruction helpers. -/
namespace Salty.Kernels.RdsumExamples
open CByte

def stride (channels : Nat) : Nat := channels+16

def inputByte (row column : Nat) : Byte := BitVec.ofNat 8 (row*13+column*19+128)

def state (rows channels : Nat) (initial : Int) : State :=
  ⟨fun name =>
    if name = "rows" then some (.integer rows)
    else if name = "channels" then some (.integer channels)
    else if name = "input" then some (.pointer 65536#64)
    else if name = "input_stride" then some (.integer (stride channels))
    else if name = "zero" then some (.pointer 4096#64)
    else if name = "output" then some (.pointer 16#64)
    else if name = "params" then some (.pointer 0#64)
    else none,
   ⟨fun a => if 16 ≤ a.toNat ∧ a.toNat < 16+4*channels then
      (bytes32 initial)[(a.toNat-16)%4]!
    else if 4096 ≤ a.toNat ∧ a.toNat < 4096+max channels 40 then 0
    else if 65536 ≤ a.toNat ∧ a.toNat < 65536+rows*stride channels then
      let offset := a.toNat-65536
      if offset%stride channels < channels then inputByte (offset/stride channels) (offset%stride channels)
      else 213
    else 165,
    fun a => (16 ≤ a.toNat ∧ a.toNat < 16+4*channels) ∨
      (4096 ≤ a.toNat ∧ a.toNat < 4096+max channels 40) ∨
      (65536 ≤ a.toNat ∧ a.toNat < 65536+rows*stride channels),
    fun a => 16 ≤ a.toNat ∧ a.toNat < 16+4*channels⟩⟩

def expected (signed : Bool) (rows channels : Nat) (initial : Int) : List Byte :=
  ((List.range channels).map (fun column =>
    let sum := (List.range rows).foldl (fun acc row => acc+
      (if signed then (inputByte row column).toInt else (inputByte row column).toNat)) initial
    bytes32 sum)).flatten

def check (cfg : Config) (code : Stmt) (signed : Bool) (rows channels : Nat) (initial : Int) : Bool :=
  match run cfg 8192 code (state rows channels initial) with
  | none => false
  | some result =>
      readBytes result.memory 16#64 (4*channels) == expected signed rows channels initial &&
      result.memory.data 15#64 == 165 && result.memory.data (BitVec.ofNat 64 (16+4*channels)) == 165

end Salty.Kernels.RdsumExamples
