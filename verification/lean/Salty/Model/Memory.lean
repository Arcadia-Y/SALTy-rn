import Std

/-! Review-facing definitions. Supporting lemmas live in `Salty.Proofs.Core.Memory`. -/

namespace Salty

abbrev Address := BitVec 64
abbrev Byte := BitVec 8

/-- Byte-addressed memory with separate read/write permissions. Addresses and
address arithmetic are 64-bit words; no implicit unbounded integer pointers. -/
structure Memory where
  data : Address → Byte
  readable : Address → Bool
  writable : Address → Bool

namespace Memory
def load (m : Memory) (a : Address) : Option Byte :=
  if m.readable a then some (m.data a) else none

def write (m : Memory) (a : Address) (b : Byte) : Memory :=
  { m with data := fun p => if p = a then b else m.data p }

def store (m : Memory) (a : Address) (b : Byte) : Option Memory :=
  if m.writable a then some (m.write a b) else none

/-- Input and output regions are explicit sets of byte addresses. Disjointness
is a precondition when different vector schedules can change alias behavior. -/
def Disjoint (left right : Address → Prop) : Prop := ∀ a, left a → ¬ right a

/-- The caller observes all bytes in a chosen footprint. A complete contract
must also prove a frame property for every writable byte outside this footprint. -/
def AgreeOn (region : Address → Prop) (a b : Memory) : Prop :=
  ∀ p, region p → a.data p = b.data p
end Memory
end Salty
