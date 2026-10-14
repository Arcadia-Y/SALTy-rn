import Salty.Proofs.Core.CByteMemory
import Salty.Proofs.Core.CWordMemory

namespace Salty.CByte

theorem replaceWord_length (old word : List Byte) (lane : Nat)
    (ho : old.length = 8) (hw : word.length = 4) (hl : lane < 2) :
    (replaceWord old word lane).length = 8 := by
  rcases (show lane = 0 ∨ lane = 1 by omega) with rfl | rfl <;>
    simp [replaceWord, ho, hw]

/-- Complete pairs of word loads erase the prior NEON lane contents. -/
theorem replaceWord_pair (old left right : List Byte)
    (ho : old.length = 8) (hl : left.length = 4) :
    replaceWord (replaceWord old left 0) right 1 = left ++ right := by
  simp [replaceWord, hl, ho, List.take_append, List.drop_append]

/-- A segment contains exactly two complete four-byte fields. -/
theorem interleaveWords_length (left right : List Byte) (n : Nat)
    (hl : 4*n ≤ left.length) (hr : 4*n ≤ right.length) :
    (interleaveWords left right n).length = 8*n := by
  induction n generalizing left right with
  | zero => rfl
  | succ n ih =>
    have l4 : 4 ≤ left.length := by omega
    have r4 : 4 ≤ right.length := by omega
    simp only [interleaveWords, List.length_append, List.length_take, List.length_drop]
    rw [Nat.min_eq_left l4, Nat.min_eq_left r4,
      ih (left.drop 4) (right.drop 4) (by simp; omega) (by simp; omega)]
    omega

/-- Splitting a sequence of segments agrees with advancing both vector fields
by the same number of words. -/
theorem interleaveWords_add (left right : List Byte) (n k : Nat) :
    interleaveWords left right (n+k) = interleaveWords left right n ++
      interleaveWords (left.drop (4*n)) (right.drop (4*n)) k := by
  induction n generalizing left right with
  | zero => simp [interleaveWords]
  | succ n ih =>
    simp only [Nat.succ_add, interleaveWords, ih, List.append_assoc, List.drop_drop]
    simp only [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    rw [show (0 + 4*n).succ.succ.succ.succ = 4*n + 4*1 by omega]

/-- Extra vector suffix bytes do not affect the first n stored segments. -/
theorem interleaveWords_take (left right : List Byte) (n : Nat) :
    interleaveWords (left.take (4*n)) (right.take (4*n)) n = interleaveWords left right n := by
  induction n generalizing left right with
  | zero => rfl
  | succ n ih =>
    simp only [interleaveWords, List.take_take, List.drop_take]
    have size : 4*(n+1)-4 = 4*n := by omega
    have enough : min 4 (4*(n+1)) = 4 := by omega
    rw [size, enough, ih]

/-- The modeled segment-store guard makes all byte destinations distinct,
even if the base is near the modular address boundary. -/
theorem segment_byte_injective (base : Address) (n : Nat) (bound : 8*n ≤ 2^64)
    (i j : Nat) (hi : i < 8*n) (hj : j < 8*n)
    (same : base + BitVec.ofNat 64 i = base + BitVec.ofNat 64 j) : i = j := by
  have bits : BitVec.ofNat 64 i = BitVec.ofNat 64 j := (BitVec.add_right_inj base).mp same
  have numbers := congrArg BitVec.toNat bits
  simp only [BitVec.toNat_ofNat] at numbers
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at numbers
  exact numbers

/-- Contiguous word stores and one byte-block write have identical memory. -/
theorem writeStrided32_contiguous (m : Memory) (base : Address) (bs : List Byte) (n : Nat)
    (length : bs.length = 4*n) :
    writeStrided32 m base 4 bs n = writeBytes m base bs := by
  induction n generalizing m base bs with
  | zero =>
    have empty : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst bs
    rfl
  | succ n ih =>
    have len : (bs.take 4).length = 4 := by simp; omega
    have tailLen : (bs.drop 4).length = 4*n := by simp; omega
    rw [writeStrided32, ih _ _ _ tailLen]
    have split := writeBytes_append m base (bs.take 4) (bs.drop 4)
    rw [List.take_append_drop, len] at split
    exact split.symm

/-- Every permutation of segment fields reaches the same final memory as the
actual guarded effect. All fields are four-byte words at distinct offsets. -/
theorem storeSegment2_any_order (m : Memory) (base : Address) (left right : List Byte) (n : Nat)
    (hl : 4*n ≤ left.length) (hr : 4*n ≤ right.length) (bound : 8*n ≤ 2^64)
    (safe : ∀ p, Footprint base (8*n) p → m.writable p = true)
    (order : List Nat) (permutation : (List.range (2*n)).Perm order) :
    effect m .storeSegment2U32RVV [.pointer base, .vectors 4 [left,right], .integer n] =
      some (order.foldl (fun mem lane => writeLane32 mem base 4 (interleaveWords left right n) lane) m) := by
  have len := interleaveWords_length left right n hl hr
  have stored := storeBytes_success m base (interleaveWords left right n) (by simpa [len] using safe)
  have layout : DisjointStride32 (4#64) (2*n) := by
    right
    simp only [BitVec.toNat_ofNat]
    constructor
    · decide
    · omega
  have sequential := writeStrided32_contiguous m base (interleaveWords left right n) (2*n) (by omega)
  rw [writeStrided32_lane_order] at sequential
  rw [← sequential, strided_lane_order_independent m base 4 (interleaveWords left right n)
    (2*n) (List.range (2*n)) order layout permutation (by intro i hi; simpa using hi)] at stored
  simpa [effect, hl, hr, bound] using stored

end Salty.CByte
