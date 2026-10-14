import Salty.Proofs.Rdsum.ScheduleOriginal

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- Masking rows beyond the original interval contributes exactly zero. -/
theorem masked_range_sum (kind : Interpretation) (rows padded : Nat) (f : Nat → Byte)
    (bound : rows ≤ padded) :
    sumWords (widen32 kind ((List.range padded).map (fun i => if i < rows then f i else 0))) =
      sumWords (widen32 kind ((List.range rows).map f)) := by
  have range : List.range padded = List.range rows ++ (List.range (padded-rows)).map (rows+·) := by
    conv => lhs; rw [show padded = rows+(padded-rows) by omega]
    exact List.range_add
  have front : (List.range rows).map (fun i => if i < rows then f i else 0) = (List.range rows).map f := by
    apply List.map_congr_left
    intro i hi
    simp [List.mem_range.mp hi]
  have back : (List.range (padded-rows)).map (fun i => if rows+i < rows then f (rows+i) else (0 : Byte)) =
      List.replicate (padded-rows) 0 := by
    simp only [show ∀ i, ¬ rows+i < rows from fun i => by omega, ↓reduceIte, List.map_const', List.length_range]
  rw [range, List.map_append, List.map_map, front]
  change sumWords (widen32 kind (((List.range rows).map f) ++
    (List.range (padded-rows)).map (fun i => if rows+i < rows then f (rows+i) else 0))) = _
  rw [back]
  simp only [widen32, List.map_append, sumWords_append]
  rw [show sumWords (List.map (fun x : Byte => BitVec.ofInt 32 (value kind x))
      (List.replicate (padded-rows) 0)) = 0 from sum_widen_zero kind (padded-rows)]
  simp

/-- Original-memory sum of one consecutive row interval. -/
def intervalSum (kind : Interpretation) (m : Memory) (input : Address)
    (stride first rows column : Nat) : BitVec 32 :=
  sumWords (widen32 kind ((List.range rows).map (fun i =>
    m.data (input+BitVec.ofNat 64 ((first+i)*stride+column)))))

theorem scheduled_sum_original (kind : Interpretation) (m : Memory) (input zero : Address)
    (stride column count first rows : Nat) (pointers : Nat → Address) (counted : GroupCount count rows)
    (zeros : m.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < rows → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    sumWords (widen32 kind ((scheduledRows m zero (7*stride) count pointers rows).map (fun row => row column))) =
      intervalSum kind m input stride first rows column := by
  rw [scheduledRows_original m input zero stride column count first rows pointers counted zeros
    (fun i hi live => ptrs i hi (by omega))]
  simp only [Int.ofNat_lt]
  apply masked_range_sum
  have bound := counted.1
  unfold GroupCount at counted
  omega

/-- The bounded 16-bit loop and its widening agree with the original interval's
32-bit column sums, including incomplete groups of seven. -/
theorem widen_groupFold_original (kind : Interpretation) (m : Memory) (input zero : Address)
    (width stride count first rows : Nat) (pointers : Nat → Address) (initial : Nat → BitVec 32)
    (counted : GroupCount count rows) (small : 7*count ≤ 256)
    (zeros : ∀ column, column < width → m.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < rows → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    WideningISA.widenAdd32 kind ((List.range width).map initial)
      (groupFold kind m zero width (7*stride) count pointers rows
        ((List.range width).map (fun _ => 0))).acc =
      (List.range width).map (fun column => initial column + intervalSum kind m input stride first rows column) := by
  rw [widen_groupFold kind m zero width (7*stride) count pointers rows initial small]
  apply List.map_congr_left
  intro column hc
  rw [scheduled_sum_original kind m input zero stride column count first rows pointers counted
    (zeros column (List.mem_range.mp hc)) ptrs]

end Salty.Kernels.Rdsum
