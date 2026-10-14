import Salty.Proofs.Core.ReductionISA

/-! Loop-invariant algebra for the two integer reductions. These folds model
accumulator arithmetic only; their connection to extracted control flow and
memory accesses must be established separately. -/
namespace Salty.ReductionISA

/-- Any finite sequence of active prefixes, including shorter prefixes before
later longer ones, preserves the full modular sum when tails are undisturbed. -/
theorem prefix_fold_sum (old : List (BitVec 32)) (chunks : List (List (BitVec 32)))
    (bounds : ∀ xs ∈ chunks, xs.length ≤ old.length) :
    (chunks.foldl addPrefix old).length = old.length ∧
    sumWords (chunks.foldl addPrefix old) = sumWords old + sumWords chunks.flatten := by
  induction chunks generalizing old with
  | nil => simp [sumWords]
  | cons xs chunks ih =>
    have hx := bounds xs (by simp)
    have len := addPrefix_length old xs hx
    have next := ih (addPrefix old xs) (fun ys hy => by rw [len]; exact bounds ys (by simp [hy]))
    simp only [List.foldl_cons]
    constructor
    · exact next.1.trans len
    · rw [next.2, addPrefix_sum old xs hx, List.flatten_cons, sumWords_append, BitVec.add_assoc]

/-- The source's inner loop has at most128 loads of16 bytes. This invariant
tracks every halfword's range as well as the accumulated modular32 sum. -/
theorem pair_fold_invariant (kind : Interpretation) (k : Nat)
    (acc : List (BitVec 16)) (chunks : List (List (BitVec 8)))
    (ha : acc.length = 8) (sizes : ∀ xs ∈ chunks, xs.length = 16)
    (bounds : ∀ a ∈ acc, LaneBound kind k a) (limit : k + chunks.length ≤ 128) :
    (chunks.foldl (pairAcc16 kind) acc).length = 8 ∧
    (∀ a ∈ chunks.foldl (pairAcc16 kind) acc, LaneBound kind (k + chunks.length) a) ∧
    sumWords (widen32 kind (chunks.foldl (pairAcc16 kind) acc)) =
      sumWords (widen32 kind acc) + sumWords (widen32 kind chunks.flatten) := by
  induction chunks generalizing k acc with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero, List.flatten_nil]
    refine ⟨ha, bounds, ?_⟩
    simp [widen32, sumWords]
  | cons xs chunks ih =>
    have hk : k < 128 := by simp only [List.length_cons] at limit; omega
    have hx : xs.length = 2 * acc.length := by rw [ha, sizes xs (by simp)]
    have len : (pairAcc16 kind acc xs).length = 8 := (pairAcc16_length kind acc xs hx).trans ha
    have next := ih (k + 1) (pairAcc16 kind acc xs) len
      (fun ys hy => sizes ys (by simp [hy]))
      (pairAcc16_bounds kind k hk acc xs bounds)
      (by simp only [List.length_cons] at limit; omega)
    simp only [List.foldl_cons, List.length_cons]
    refine ⟨next.1, ?_, ?_⟩
    · simpa only [Nat.add_assoc, Nat.add_comm 1 chunks.length] using next.2.1
    · rw [next.2.2, pairAcc16_sum kind k hk acc xs hx bounds, List.flatten_cons]
      simp only [widen32, List.map_append, sumWords_append, BitVec.add_assoc]

end Salty.ReductionISA
