import Salty.Model.ReductionISA
import Std

/-! Integer reduction instruction infrastructure. The lemmas here are about
lane operations; they do not assert equivalence of either extracted C kernel.
All 32-bit additions wrap, while the NEON byte-to-halfword accumulation needs
an explicit bound before its result can be widened without losing information. -/
namespace Salty.ReductionISA

/-- After k pair accumulations, this lane represents 2*k byte inputs. -/
def LaneBound (kind : Interpretation) (k : Nat) (acc : BitVec 16) : Prop :=
  match kind with
  | .signed => -256 * (k : Int) ≤ acc.toInt ∧ acc.toInt ≤ 254 * (k : Int)
  | .unsigned => (acc.toNat : Int) ≤ 510 * (k : Int)

/-- Literal table in both source reductions: sixteen ones, then sixteen zeroes. -/
def oneMaskTable : List (BitVec 8) := List.replicate 16 1 ++ List.replicate 16 0

def tailMask (n : Nat) : List (BitVec 8) := (oneMaskTable.drop (16 - n)).take 16

@[simp] theorem sumWords_nil : sumWords [] = 0 := rfl
@[simp] theorem sumWords_cons (x : BitVec 32) (xs) : sumWords (x :: xs) = x + sumWords xs := rfl

theorem sumWords_append (xs ys : List (BitVec 32)) :
    sumWords (xs ++ ys) = sumWords xs + sumWords ys := by
  induction xs with
  | nil => simp [sumWords]
  | cons x xs ih => simp [sumWords, ih, BitVec.add_assoc]

theorem sumInts_append (xs ys : List Int) :
    sumInts (xs ++ ys) = sumInts xs + sumInts ys := by
  induction xs with
  | nil => simp [sumInts]
  | cons x xs ih => simp [sumInts, ih, Int.add_assoc]

theorem sumWords_ofInt (xs : List Int) :
    sumWords (xs.map (BitVec.ofInt 32)) = BitVec.ofInt 32 (sumInts xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumWords, sumInts, ih, BitVec.ofInt_add]

theorem sum_pairSums (xs : List Int) : sumInts (pairSums xs) = sumInts xs := by
  induction xs using pairSums.induct with
  | case1 => rfl
  | case2 x => rfl
  | case3 x y xs ih => simp [pairSums, sumInts, ih, Int.add_assoc]

theorem sumWords_zipWith_add (xs ys : List (BitVec 32)) (hlen : xs.length = ys.length) :
    sumWords (List.zipWith (· + ·) xs ys) = sumWords xs + sumWords ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [sumWords]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zipWith_cons_cons, sumWords, ih ys hlen]
      simp only [BitVec.add_assoc]
      congr 1
      rw [← BitVec.add_assoc y, BitVec.add_comm y (sumWords xs), BitVec.add_assoc]

theorem addPrefix_length (old active : List (BitVec 32)) (h : active.length ≤ old.length) :
    (addPrefix old active).length = old.length := by
  simp [addPrefix, List.length_zipWith, Nat.min_eq_left h]
  omega

theorem addPrefix_sum (old active : List (BitVec 32)) (h : active.length ≤ old.length) :
    sumWords (addPrefix old active) = sumWords old + sumWords active := by
  have lengths : (old.take active.length).length = active.length := by simp [Nat.min_eq_left h]
  rw [addPrefix, sumWords_append, sumWords_zipWith_add _ _ lengths]
  have split := sumWords_append (old.take active.length) (old.drop active.length)
  rw [List.take_append_drop] at split
  rw [split]
  simp only [BitVec.add_assoc]
  rw [BitVec.add_comm (sumWords active)]

theorem addPrefix_tail (old active : List (BitVec 32)) (h : active.length ≤ old.length) :
    (addPrefix old active).drop active.length = old.drop active.length := by
  have len : (List.zipWith (· + ·) (old.take active.length) active).length = active.length := by
    simp [List.length_zipWith, Nat.min_eq_left h]
  unfold addPrefix
  simpa only [len] using (List.drop_left (l₁ := List.zipWith (· + ·) (old.take active.length) active)
    (l₂ := old.drop active.length))

theorem byte_bounds (kind : Interpretation) (x : BitVec 8) :
    (match kind with | .signed => -128 | .unsigned => 0) ≤ value kind x ∧
    value kind x ≤ (match kind with | .signed => 127 | .unsigned => 255) := by
  cases kind with
  | signed =>
    have lo := BitVec.le_toInt x
    have hi := BitVec.toInt_lt (x := x)
    simp only [value]
    constructor <;> omega
  | unsigned =>
    have hi := BitVec.isLt x
    simp only [value]
    constructor <;> omega

theorem laneBound_zero (kind : Interpretation) : LaneBound kind 0 0 := by
  cases kind <;> simp [LaneBound]

theorem addPair16_eq_ofInt (kind : Interpretation) (acc : BitVec 16) (x y : BitVec 8) :
    addPair16 kind acc x y = BitVec.ofInt 16 (value kind acc + value kind x + value kind y) := by
  cases kind <;> simp [addPair16, value, BitVec.ofInt_add, BitVec.add_assoc]

/-- 128 updates are safe even for -128 or 255 in every source byte. -/
theorem addPair16_exact (kind : Interpretation) (k : Nat) (hk : k < 128)
    (acc : BitVec 16) (x y : BitVec 8) (bound : LaneBound kind k acc) :
    value kind (addPair16 kind acc x y) = value kind acc + value kind x + value kind y := by
  have bx := byte_bounds kind x
  have byBound := byte_bounds kind y
  rw [addPair16_eq_ofInt]
  cases kind with
  | signed =>
    simp only [value] at *
    simp only [LaneBound] at bound
    apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega
  | unsigned =>
    simp only [value] at *
    simp only [LaneBound] at bound
    rw [BitVec.toNat_ofInt]
    have nonneg : 0 ≤ (acc.toNat : Int) + x.toNat + y.toNat := by omega
    have small : (acc.toNat : Int) + x.toNat + y.toNat < 65536 := by omega
    change ((( (acc.toNat : Int) + x.toNat + y.toNat) % 65536).toNat : Int) = _
    rw [Int.emod_eq_of_lt nonneg small, Int.toNat_of_nonneg nonneg]

theorem addPair16_bound (kind : Interpretation) (k : Nat) (hk : k < 128)
    (acc : BitVec 16) (x y : BitVec 8) (bound : LaneBound kind k acc) :
    LaneBound kind (k + 1) (addPair16 kind acc x y) := by
  have exact := addPair16_exact kind k hk acc x y bound
  have bx := byte_bounds kind x
  have byBound := byte_bounds kind y
  cases kind <;> simp only [LaneBound, value] at * <;> omega

theorem pairAcc16_length (kind : Interpretation) (acc : List (BitVec 16))
    (xs : List (BitVec 8)) (hlen : xs.length = 2 * acc.length) :
    (pairAcc16 kind acc xs).length = acc.length := by
  induction acc generalizing xs with
  | nil => simp [pairAcc16]
  | cons a acc ih =>
    cases xs with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons x xs =>
      cases xs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons y xs =>
        have len : xs.length = 2 * acc.length := by simp only [List.length_cons] at hlen; omega
        simp [pairAcc16, ih xs len]

theorem pairAcc16_bounds (kind : Interpretation) (k : Nat) (hk : k < 128)
    (acc : List (BitVec 16)) (xs : List (BitVec 8))
    (bounds : ∀ a ∈ acc, LaneBound kind k a) :
    ∀ a ∈ pairAcc16 kind acc xs, LaneBound kind (k + 1) a := by
  induction acc generalizing xs with
  | nil => simp [pairAcc16]
  | cons a acc ih =>
    cases xs with
    | nil => simp [pairAcc16]
    | cons x xs =>
      cases xs with
      | nil => simp [pairAcc16]
      | cons y xs =>
        intro z hz
        simp only [pairAcc16, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact addPair16_bound kind k hk a x y (bounds a (by simp))
        · exact ih xs (fun b hb => bounds b (by simp [hb])) z hz

theorem pairAcc16_value_sum (kind : Interpretation) (k : Nat) (hk : k < 128)
    (acc : List (BitVec 16)) (xs : List (BitVec 8))
    (hlen : xs.length = 2 * acc.length) (bounds : ∀ a ∈ acc, LaneBound kind k a) :
    sumInts ((pairAcc16 kind acc xs).map (value kind)) =
      sumInts (acc.map (value kind)) + sumInts (xs.map (value kind)) := by
  induction acc generalizing xs with
  | nil =>
    have : xs = [] := by simpa using hlen
    subst xs
    rfl
  | cons a acc ih =>
    cases xs with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons x xs =>
      cases xs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons y xs =>
        have len : xs.length = 2 * acc.length := by simp only [List.length_cons] at hlen; omega
        have rest := ih xs len (fun b hb => bounds b (by simp [hb]))
        have lane := addPair16_exact kind k hk a x y (bounds a (by simp))
        simp only [pairAcc16, List.map_cons, sumInts, lane, rest]
        omega

theorem sum_widen32 (kind : Interpretation) (xs : List (BitVec w)) :
    sumWords (widen32 kind xs) = BitVec.ofInt 32 (sumInts (xs.map (value kind))) := by
  simpa [widen32, List.map_map] using sumWords_ofInt (xs.map (value kind))

theorem pairAcc16_sum (kind : Interpretation) (k : Nat) (hk : k < 128)
    (acc : List (BitVec 16)) (xs : List (BitVec 8))
    (hlen : xs.length = 2 * acc.length) (bounds : ∀ a ∈ acc, LaneBound kind k a) :
    sumWords (widen32 kind (pairAcc16 kind acc xs)) =
      sumWords (widen32 kind acc) + sumWords (widen32 kind xs) := by
  rw [sum_widen32, sum_widen32, sum_widen32, pairAcc16_value_sum kind k hk acc xs hlen bounds,
    BitVec.ofInt_add]

theorem pairAcc32_length (kind : Interpretation) (acc : List (BitVec 32))
    (xs : List (BitVec 16)) (hlen : xs.length = 2 * acc.length) :
    (pairAcc32 kind acc xs).length = acc.length := by
  induction acc generalizing xs with
  | nil => simp [pairAcc32]
  | cons a acc ih =>
    cases xs with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons x xs =>
      cases xs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons y xs =>
        have len : xs.length = 2 * acc.length := by simp only [List.length_cons] at hlen; omega
        simp [pairAcc32, ih xs len]

theorem add_four (a b c d : BitVec 32) : (a + b) + (c + d) = (a + c) + (b + d) := by
  simp only [BitVec.add_assoc]
  congr 1
  rw [← BitVec.add_assoc b, BitVec.add_comm b c, BitVec.add_assoc]

/-- This stage needs no range precondition: its modular32 result is the
observable integer reduction, including sums that exceed the signed range. -/
theorem pairAcc32_sum (kind : Interpretation) (acc : List (BitVec 32))
    (xs : List (BitVec 16)) (hlen : xs.length = 2 * acc.length) :
    sumWords (pairAcc32 kind acc xs) = sumWords acc + sumWords (widen32 kind xs) := by
  induction acc generalizing xs with
  | nil =>
    have : xs = [] := by simpa using hlen
    subst xs
    rfl
  | cons a acc ih =>
    cases xs with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons x xs =>
      cases xs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons y xs =>
        have len : xs.length = 2 * acc.length := by simp only [List.length_cons] at hlen; omega
        simp only [pairAcc32, sumWords, ih xs len, widen32, List.map_cons]
        rw [add_four, BitVec.ofInt_add]
        simp only [BitVec.add_assoc]

theorem tailMask_eq (n : Nat) (hn : n ≤ 16) :
    tailMask n = List.replicate n 1 ++ List.replicate (16 - n) 0 := by
  unfold tailMask oneMaskTable
  rw [List.drop_append_of_le_length (by simp), List.drop_replicate]
  rw [show 16 - (16 - n) = n by omega]
  rw [List.take_append_eq_append_take]
  simp only [List.take_replicate, List.length_replicate]
  rw [Nat.min_eq_right hn, Nat.min_eq_left (by omega)]

theorem zip_mul_one (xs : List (BitVec 8)) :
    List.zipWith (· * ·) xs (List.replicate xs.length 1) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons]
    rw [ih]
    simp

theorem zip_mul_zero (xs : List (BitVec 8)) :
    List.zipWith (· * ·) xs (List.replicate xs.length 0) = List.replicate xs.length 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons]
    rw [ih]
    simp

theorem masked_tail_eq (xs : List (BitVec 8)) (n : Nat) (hx : xs.length = 16) (hn : n ≤ 16) :
    List.zipWith (· * ·) xs (tailMask n) = xs.take n ++ List.replicate (16 - n) 0 := by
  have takeLength : (xs.take n).length = n := by simp [hx, Nat.min_eq_left hn]
  have dropLength : (xs.drop n).length = 16 - n := by simp [hx]
  rw [tailMask_eq n hn]
  calc
    _ = List.zipWith (· * ·) (xs.take n ++ xs.drop n)
          (List.replicate n 1 ++ List.replicate (16 - n) 0) := by rw [List.take_append_drop]
    _ = List.zipWith (· * ·) (xs.take n) (List.replicate n 1) ++
          List.zipWith (· * ·) (xs.drop n) (List.replicate (16 - n) 0) := by
      apply List.zipWith_append
      simp only [List.length_replicate, takeLength]
    _ = _ := by
      have ones := zip_mul_one (xs.take n)
      have zeros := zip_mul_zero (xs.drop n)
      rw [takeLength] at ones
      rw [dropLength] at zeros
      rw [ones, zeros]

theorem sum_widen_zero (kind : Interpretation) (n : Nat) :
    sumWords (widen32 kind (List.replicate n (0 : BitVec w))) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => cases kind <;> simpa [widen32, value, sumWords, List.replicate_succ] using ih

/-- The table multiplication discards all padded bytes, even when padding has
nonzero values. Only the first n source bytes contribute to the reduction. -/
theorem masked_tail_sum (kind : Interpretation) (xs : List (BitVec 8)) (n : Nat)
    (hx : xs.length = 16) (hn : n ≤ 16) :
    sumWords (widen32 kind (List.zipWith (· * ·) xs (tailMask n))) =
      sumWords (widen32 kind (xs.take n)) := by
  rw [masked_tail_eq xs n hx hn]
  simp only [widen32, List.map_append, sumWords_append]
  rw [show sumWords (List.map (fun x : BitVec 8 => BitVec.ofInt 32 (value kind x))
      (List.replicate (16 - n) 0)) = 0 from sum_widen_zero kind (16 - n)]
  simp

end Salty.ReductionISA
