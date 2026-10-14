import Salty.Proofs.Rdsum.BatchSum

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- Exact count of iterations of the signed decrement-by-seven loop. -/
theorem group_count_ceiling (rows : Nat) : GroupCount ((rows+6)/7) rows := by
  unfold GroupCount
  omega

theorem group_count_small (rows : Nat) (bound : rows ≤ 252) : 7*((rows+6)/7) ≤ 252 := by omega

theorem groupFold_remaining (kind : Interpretation) (m : Memory) (zero : Address) (width increment count : Nat)
    (pointers : Nat → Address) (remaining : Int) (acc : List (BitVec 16)) :
    (groupFold kind m zero width increment count pointers remaining acc).remaining = remaining-7*(count : Int) := by
  induction count generalizing pointers remaining acc with
  | zero => simp [groupFold]
  | succ count ih => simp only [groupFold, ih]; omega

theorem groupFold_length (kind : Interpretation) (m : Memory) (zero : Address) (width increment count : Nat)
    (pointers : Nat → Address) (remaining : Int) (acc : List (BitVec 16)) (ha : acc.length = width) :
    (groupFold kind m zero width increment count pointers remaining acc).acc.length = width := by
  induction count generalizing pointers remaining acc with
  | zero => exact ha
  | succ count ih =>
    apply ih
    exact rowAcc_length kind _ acc width ha (fun i => readBytes_length ..) 7

/-- Complete groups do not substitute zero rows, so every row pointer advances
by exactly count increments. Used when the 252-row batch has a successor. -/
theorem groupFold_full_pointers (kind : Interpretation) (m : Memory) (zero : Address)
    (width increment count : Nat) (pointers : Nat → Address) (remaining : Int) (acc : List (BitVec 16))
    (full : 7*(count : Int) ≤ remaining) (i : Nat) (hi : i < 7) :
    (groupFold kind m zero width increment count pointers remaining acc).pointers i =
      pointers i+BitVec.ofNat 64 (count*increment) := by
  induction count generalizing pointers remaining acc with
  | zero => simp [groupFold]
  | succ count ih =>
    rw [groupFold, ih _ (remaining-7) _ (by omega)]
    have live : ¬ (0 < i ∧ remaining ≤ (i : Int)) := by omega
    simp only [groupPointers, selectedPointers, if_neg live]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    simp [Nat.succ_mul, Nat.add_comm]

/-- Splitting a row interval preserves its exact modular column contribution. -/
theorem intervalSum_add (kind : Interpretation) (m : Memory) (input : Address)
    (stride first left right column : Nat) :
    intervalSum kind m input stride first (left+right) column =
      intervalSum kind m input stride first left column +
      intervalSum kind m input stride (first+left) right column := by
  unfold intervalSum
  rw [List.range_add, List.map_append, List.map_map]
  simp only [widen32, List.map_append, sumWords_append]
  congr 1
  simp only [List.map_map, Function.comp_def, Nat.add_assoc]

end Salty.Kernels.Rdsum
