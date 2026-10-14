import Salty.Model.CByte

/-! Review-facing definitions. Supporting lemmas live in `Salty.Proofs.Core.CByteMemory`. -/

namespace Salty.CByte

/-- The exact set of byte addresses touched by a sequential access, including
64-bit address wrap. Safe C contracts separately exclude wrap/object escape. -/
def Footprint (a : Address) (n : Nat) (p : Address) : Prop :=
  ∃ i, i < n ∧ p = a + BitVec.ofNat 64 i

def writeBytes (m : Memory) (a : Address) : List Byte → Memory
  | [] => m
  | b :: bs => writeBytes (m.write a b) (a + 1) bs

/-- Total byte view, separate from the permission-checked load operation. -/
def readBytes (m : Memory) (a : Address) : Nat → List Byte
  | 0 => []
  | n + 1 => m.data a :: readBytes m (a + 1) n

end Salty.CByte
