import Salty.Model.CByteMemory

/-! Review-facing definitions. Supporting lemmas live in `Salty.Proofs.Core.CWordMemory`. -/

/-! Byte-accurate strided 32-bit stores for the transpose/packing developments.
These definitions describe strided byte footprints and reference memory writes.
Permission, frame, and lane-permutation proofs live in the proof layer. -/
set_option maxHeartbeats 1000000
namespace Salty.CByte

def StridedFootprint (a stride : Address) (n : Nat) (p : Address) : Prop :=
  ∃ lane, lane < n ∧ Footprint (a + stride * BitVec.ofNat 64 lane) 4 p

def writeStrided32 (m : Memory) (a stride : Address) (bs : List Byte) : Nat → Memory
  | 0 => m
  | n + 1 => writeStrided32 (writeBytes m a (bs.take 4)) (a + stride) stride (bs.drop 4) n

/-- Explicit lane-order semantics used to state order independence. -/
def writeLane32 (m : Memory) (a stride : Address) (bs : List Byte) (lane : Nat) : Memory :=
  writeBytes m (a + stride * BitVec.ofNat 64 lane) ((bs.drop (4 * lane)).take 4)

end Salty.CByte
