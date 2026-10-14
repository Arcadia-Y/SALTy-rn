import Salty.Proofs.Core.WideningISA

/-! Pointwise lifting of bounded row accumulation. A row is a function from
column indices to bytes; the finite column list permits fixed NEON blocks and
arbitrary RVV active prefixes to use the same mathematical statement. -/
namespace Salty.WideningISA
open ReductionISA

theorem zipWith_map_same {α β γ δ : Type} (xs : List α) (f : α → β) (g : α → γ)
    (op : β → γ → δ) :
    List.zipWith op (xs.map f) (xs.map g) = xs.map (fun i => op (f i) (g i)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The list-level instruction fold is exactly one scalar fold per column. -/
theorem fold_rows_by_column (kind : Interpretation) (columns : List Nat)
    (rows : List (Nat → BitVec 8)) (initial : Nat → BitVec 16) :
    rows.foldl (fun acc row => widenAdd16 kind acc (columns.map row)) (columns.map initial) =
      columns.map (fun i => rows.foldl (fun acc row => addByte16 kind acc (row i)) (initial i)) := by
  induction rows generalizing initial with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.foldl, widenAdd16, zipWith_map_same]
    exact ih (fun i => addByte16 kind (initial i) (row i))

/-- Widening one bounded vector batch gives the modular 32-bit sum of its
original bytes independently for every output column. -/
theorem widen_rows (kind : Interpretation) (columns : List Nat)
    (rows : List (Nat → BitVec 8)) (initial : Nat → BitVec 32) (small : rows.length ≤ 256) :
    widenAdd32 kind (columns.map initial)
      (rows.foldl (fun acc row => widenAdd16 kind acc (columns.map row))
        (columns.map (fun _ => 0))) =
      columns.map (fun i => initial i + sumWords (widen32 kind (rows.map (fun row => row i)))) := by
  rw [fold_rows_by_column]
  unfold widenAdd32
  rw [zipWith_map_same]
  apply List.map_congr_left
  intro i hi
  simpa only [List.foldl_map] using widen_batch kind (rows.map (fun row => row i)) (initial i)
    (by simpa using small)

@[simp] theorem addByte16_zero (kind : Interpretation) (acc : BitVec 16) :
    addByte16 kind acc 0 = acc := by
  cases kind <;> simp [addByte16, value]

/-- The row substitution used for a final incomplete group contributes zero. -/
theorem fold_zero_padding (kind : Interpretation) (xs : List (BitVec 8)) (padding : Nat)
    (initial : BitVec 16) :
    (xs ++ List.replicate padding 0).foldl (addByte16 kind) initial =
      xs.foldl (addByte16 kind) initial := by
  rw [List.foldl_append]
  generalize xs.foldl (addByte16 kind) initial = acc
  induction padding with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.foldl, addByte16_zero]
    exact ih

/-- Splitting the row list at a halfword reset preserves the word contribution. -/
theorem column_sum_append (kind : Interpretation) (rows rest : List (Nat → BitVec 8)) (i : Nat) :
    sumWords (widen32 kind ((rows ++ rest).map (fun row => row i))) =
      sumWords (widen32 kind (rows.map (fun row => row i))) +
      sumWords (widen32 kind (rest.map (fun row => row i))) := by
  simp [widen32, sumWords_append]

end Salty.WideningISA
