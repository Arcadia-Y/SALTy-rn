import Salty.Model.CByteMemory

namespace Salty.CByte

structure BinarySafe (m : Memory) (a b output : Address) (n padding : Nat) : Prop where
  readA : ∀ p, Footprint a (n + padding) p → m.readable p = true
  readB : ∀ p, Footprint b (n + padding) p → m.readable p = true
  writable : ∀ p, Footprint output n p → m.writable p = true
  separateA : ∀ p, Footprint a (n + padding) p → ¬ Footprint output n p
  separateB : ∀ p, Footprint b (n + padding) p → ¬ Footprint output n p

def binaryBytes (f : Byte → Byte → Byte) (m : Memory) (a b : Address) (n : Nat) : List Byte :=
  List.zipWith f (readBytes m a n) (readBytes m b n)


def binaryResult (f : Byte → Byte → Byte) (m : Memory) (a b output : Address) (n : Nat) : Memory :=
  writeBytes m output (binaryBytes f m a b n)

end Salty.CByte
