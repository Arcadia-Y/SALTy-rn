import Salty.Spec.BinaryRegions
import Salty.Proofs.Core.CByteMemory

/-! Original-input memory specification for pointwise kernels with two byte
inputs. The inputs may alias each other; each must be separate from output.
Caller contracts separately provide live objects, alignment and no wrap. -/
namespace Salty.CByte

theorem BinarySafe.weaken_padding {m : Memory} {a b output : Address} {n padding less : Nat}
    (safe : BinarySafe m a b output n padding) (h : less ≤ padding) :
    BinarySafe m a b output n less := by
  constructor
  · intro p hp; exact safe.readA p (footprint_mono (by omega) hp)
  · intro p hp; exact safe.readB p (footprint_mono (by omega) hp)
  · exact safe.writable
  · intro p hp; exact safe.separateA p (footprint_mono (by omega) hp)
  · intro p hp; exact safe.separateB p (footprint_mono (by omega) hp)

theorem BinarySafe.advance {m : Memory} {a b output : Address} {n padding k : Nat}
    (safe : BinarySafe m a b output n padding) (hk : k ≤ n) (bs : List Byte) :
    BinarySafe (writeBytes m output bs) (a + BitVec.ofNat 64 k)
      (b + BitVec.ofNat 64 k) (output + BitVec.ofNat 64 k) (n - k) padding := by
  constructor
  · intro p hp
    rw [writeBytes_readable]
    exact safe.readA p (footprint_shift_within (by omega) hp)
  · intro p hp
    rw [writeBytes_readable]
    exact safe.readB p (footprint_shift_within (by omega) hp)
  · intro p hp
    rw [writeBytes_writable]
    exact safe.writable p (footprint_shift_within (by omega) hp)
  · intro p ha ho
    exact safe.separateA p (footprint_shift_within (by omega) ha)
      (footprint_shift_within (by omega) ho)
  · intro p hb ho
    exact safe.separateB p (footprint_shift_within (by omega) hb)
      (footprint_shift_within (by omega) ho)

/-- Both original input suffixes survive a prefix output store, including all
padding bytes required by the source's full-width tail load. -/
theorem BinarySafe.remaining_reads {m : Memory} {a b output : Address} {n padding k : Nat}
    (safe : BinarySafe m a b output n padding) (hk : k ≤ n)
    (bs : List Byte) (hlen : bs.length = k) :
    readBytes (writeBytes m output bs) (a + BitVec.ofNat 64 k) (n - k + padding) =
      readBytes m (a + BitVec.ofNat 64 k) (n - k + padding) ∧
    readBytes (writeBytes m output bs) (b + BitVec.ofNat 64 k) (n - k + padding) =
      readBytes m (b + BitVec.ofNat 64 k) (n - k + padding) := by
  constructor
  · apply readBytes_writeBytes_disjoint
    intro p hi ho
    exact safe.separateA p (footprint_shift_within (by omega) hi)
      (footprint_mono (by omega) ho)
  · apply readBytes_writeBytes_disjoint
    intro p hi ho
    exact safe.separateB p (footprint_shift_within (by omega) hi)
      (footprint_mono (by omega) ho)

@[simp] theorem binaryBytes_length (f : Byte → Byte → Byte) (m : Memory) (a b : Address) (n : Nat) :
    (binaryBytes f m a b n).length = n := by simp [binaryBytes]

theorem binaryBytes_add (f : Byte → Byte → Byte) (m : Memory) (a b : Address) (n k : Nat) :
    binaryBytes f m a b (n + k) = binaryBytes f m a b n ++
      binaryBytes f m (a + BitVec.ofNat 64 n) (b + BitVec.ofNat 64 n) k := by
  simp only [binaryBytes, readBytes_add]
  exact List.zipWith_append (by simp)

@[simp] theorem binaryResult_readable (f : Byte → Byte → Byte) (m : Memory)
    (a b output : Address) (n : Nat) :
    (binaryResult f m a b output n).readable = m.readable := by simp [binaryResult]

@[simp] theorem binaryResult_writable (f : Byte → Byte → Byte) (m : Memory)
    (a b output : Address) (n : Nat) :
    (binaryResult f m a b output n).writable = m.writable := by simp [binaryResult]

theorem binaryResult_frame (f : Byte → Byte → Byte) (m : Memory) (a b output p : Address)
    (n : Nat) (outside : ¬ Footprint output n p) :
    (binaryResult f m a b output n).data p = m.data p := by
  apply writeBytes_frame
  simpa using outside

/-- Splitting the output into any prefix and suffix preserves the exact whole
memory result, because both source input suffixes retain their original bytes. -/
theorem binaryResult_split (f : Byte → Byte → Byte) {m : Memory} {a b output : Address}
    {n k : Nat} (safe : BinarySafe m a b output n 0) (hk : k ≤ n) :
    binaryResult f m a b output n =
      binaryResult f (binaryResult f m a b output k)
        (a + BitVec.ofNat 64 k) (b + BitVec.ofNat 64 k)
        (output + BitVec.ofNat 64 k) (n - k) := by
  have reads := safe.remaining_reads hk (binaryBytes f m a b k) (by simp)
  simp only [Nat.add_zero] at reads
  have split : n = k + (n - k) := by omega
  conv => lhs; unfold binaryResult; rw [split, binaryBytes_add, writeBytes_append]
  simp only [binaryBytes_length]
  unfold binaryResult
  congr 1
  simp only [binaryBytes] at reads
  simp only [binaryBytes, reads.1, reads.2]

end Salty.CByte
