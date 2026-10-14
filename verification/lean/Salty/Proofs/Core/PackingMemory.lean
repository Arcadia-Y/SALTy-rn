import Salty.Proofs.Core.CPacking

/-! Original-input memory specification for interleaved packing with two word streams. The input streams may alias each
other; both are separate from the output. This is memory infrastructure only. -/
namespace Salty.CByte

structure PairSafe (m : Memory) (a b output : Address) (n : Nat) : Prop where
  readA : ∀ p, Footprint a (4*n) p → m.readable p = true
  readB : ∀ p, Footprint b (4*n) p → m.readable p = true
  writable : ∀ p, Footprint output (8*n) p → m.writable p = true
  separateA : ∀ p, Footprint a (4*n) p → ¬ Footprint output (8*n) p
  separateB : ∀ p, Footprint b (4*n) p → ¬ Footprint output (8*n) p

theorem PairSafe.prefix {m : Memory} {a b output : Address} {n k : Nat}
    (safe : PairSafe m a b output n) (hk : k ≤ n) : PairSafe m a b output k := by
  constructor
  · intro p hp; exact safe.readA p (footprint_mono (by omega) hp)
  · intro p hp; exact safe.readB p (footprint_mono (by omega) hp)
  · intro p hp; exact safe.writable p (footprint_mono (by omega) hp)
  · intro p hi ho; exact safe.separateA p (footprint_mono (by omega) hi) (footprint_mono (by omega) ho)
  · intro p hi ho; exact safe.separateB p (footprint_mono (by omega) hi) (footprint_mono (by omega) ho)

theorem PairSafe.advance {m : Memory} {a b output : Address} {n k : Nat}
    (safe : PairSafe m a b output n) (hk : k ≤ n) (bs : List Byte) :
    PairSafe (writeBytes m output bs) (a + BitVec.ofNat 64 (4*k))
      (b + BitVec.ofNat 64 (4*k)) (output + BitVec.ofNat 64 (8*k)) (n - k) := by
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

/-- Both original word-stream suffixes survive a prefix segment store. -/
theorem PairSafe.remaining_reads {m : Memory} {a b output : Address} {n k : Nat}
    (safe : PairSafe m a b output n) (hk : k ≤ n)
    (bs : List Byte) (hlen : bs.length = 8*k) :
    readBytes (writeBytes m output bs) (a + BitVec.ofNat 64 (4*k)) (4*(n-k)) =
      readBytes m (a + BitVec.ofNat 64 (4*k)) (4*(n-k)) ∧
    readBytes (writeBytes m output bs) (b + BitVec.ofNat 64 (4*k)) (4*(n-k)) =
      readBytes m (b + BitVec.ofNat 64 (4*k)) (4*(n-k)) := by
  constructor
  · apply readBytes_writeBytes_disjoint
    intro p hi ho
    exact safe.separateA p (footprint_shift_within (by omega) hi)
      (footprint_mono (by omega) ho)
  · apply readBytes_writeBytes_disjoint
    intro p hi ho
    exact safe.separateB p (footprint_shift_within (by omega) hi)
      (footprint_mono (by omega) ho)


def pairBytes (m : Memory) (a b : Address) (n : Nat) : List Byte :=
  interleaveWords (readBytes m a (4*n)) (readBytes m b (4*n)) n

@[simp] theorem pairBytes_length (m : Memory) (a b : Address) (n : Nat) :
    (pairBytes m a b n).length = 8*n :=
  interleaveWords_length _ _ n (by simp) (by simp)

theorem pairBytes_add (m : Memory) (a b : Address) (n k : Nat) :
    pairBytes m a b (n+k) = pairBytes m a b n ++
      pairBytes m (a+BitVec.ofNat 64 (4*n)) (b+BitVec.ofNat 64 (4*n)) k := by
  have prefixPart := interleaveWords_take (readBytes m a (4*(n+k))) (readBytes m b (4*(n+k))) n
  rw [readBytes_take m a (4*n) (4*(n+k)) (by omega),
      readBytes_take m b (4*n) (4*(n+k)) (by omega)] at prefixPart
  have suffixPart (base : Address) :
      (readBytes m base (4*(n+k))).drop (4*n) = readBytes m (base+BitVec.ofNat 64 (4*n)) (4*k) := by
    rw [Nat.mul_add, readBytes_add]
    simpa only [readBytes_length] using (List.drop_left
      (l₁ := readBytes m base (4*n)) (l₂ := readBytes m (base+BitVec.ofNat 64 (4*n)) (4*k)))
  unfold pairBytes
  rw [interleaveWords_add, ← prefixPart, suffixPart a, suffixPart b]

def pairResult (m : Memory) (a b output : Address) (n : Nat) : Memory :=
  writeBytes m output (pairBytes m a b n)

@[simp] theorem pairResult_readable (m : Memory) (a b output : Address) (n : Nat) :
    (pairResult m a b output n).readable = m.readable := by simp [pairResult]

@[simp] theorem pairResult_writable (m : Memory) (a b output : Address) (n : Nat) :
    (pairResult m a b output n).writable = m.writable := by simp [pairResult]

theorem pairResult_frame (m : Memory) (a b output p : Address) (n : Nat)
    (outside : ¬ Footprint output (8*n) p) : (pairResult m a b output n).data p = m.data p := by
  apply writeBytes_frame
  simpa using outside

/-- Arbitrary progressing chunks give the same interleaved original-input
memory result; the input streams may overlap each other. -/
theorem pairResult_split {m : Memory} {a b output : Address} {n k : Nat}
    (safe : PairSafe m a b output n) (hk : k ≤ n) :
    pairResult m a b output n =
      pairResult (pairResult m a b output k)
        (a+BitVec.ofNat 64 (4*k)) (b+BitVec.ofNat 64 (4*k))
        (output+BitVec.ofNat 64 (8*k)) (n-k) := by
  have reads := safe.remaining_reads hk (pairBytes m a b k) (by simp)
  have partition := pairBytes_add m a b k (n-k)
  rw [show k+(n-k) = n by omega] at partition
  unfold pairResult
  rw [partition, writeBytes_append, pairBytes_length]
  congr 1
  simp only [pairBytes] at reads
  simp only [pairBytes, reads.1, reads.2]

end Salty.CByte
