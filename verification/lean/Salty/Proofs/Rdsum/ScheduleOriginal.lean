import Salty.Proofs.Rdsum.Schedule

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- Still-live row pointers advance by precisely seven strides. -/
theorem groupPointers_live (input zero : Address) (stride first : Nat) (remaining : Int)
    (pointers : Nat → Address)
    (ptrs : ∀ (i : Nat), i < 7 → (i : Int) < remaining →
      pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∀ (i : Nat), i < 7 → (i : Int) < remaining-7 →
      groupPointers pointers zero remaining (7*stride) i = input+BitVec.ofNat 64 ((first+7+i)*stride) := by
  intro i hi live
  have current : (i : Int) < remaining := by omega
  have absent : ¬ (0 < i ∧ remaining ≤ (i : Int)) := by omega
  simp only [groupPointers, selectedPointers, if_neg absent, ptrs i hi current]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  simp only [Nat.add_mul]
  omega

/-- Selected scalar byte: a live original row or an actual zero-buffer byte. -/
theorem selectedRow_original (m : Memory) (input zero : Address) (stride first column : Nat)
    (remaining : Int) (pointers : Nat → Address) (positive : 0 < remaining)
    (zeros : m.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → (i : Int) < remaining →
      pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) (i : Nat) (hi : i < 7) :
    selectedRow m pointers zero remaining i column =
      if (i : Int) < remaining then m.data (input+BitVec.ofNat 64 ((first+i)*stride+column)) else 0 := by
  by_cases live : (i : Int) < remaining
  · have absent : ¬ (0 < i ∧ remaining ≤ (i : Int)) := by omega
    simp only [selectedRow, selectedPointers, if_neg absent, if_pos live, ptrs i hi live]
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  · have absent : 0 < i ∧ remaining ≤ (i : Int) := by omega
    simp only [selectedRow, selectedPointers, if_pos absent, if_neg live, zeros]

/-- The entire selected scalar schedule is the original consecutive rows,
followed only by zero-buffer padding to the next multiple of seven. -/
theorem scheduledRows_original (m : Memory) (input zero : Address) (stride column count first : Nat)
    (remaining : Int) (pointers : Nat → Address) (counted : GroupCount count remaining)
    (zeros : m.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → (i : Int) < remaining →
      pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    (scheduledRows m zero (7*stride) count pointers remaining).map (fun row => row column) =
      (List.range (7*count)).map (fun (i : Nat) => if (i : Int) < remaining then
        m.data (input+BitVec.ofNat 64 ((first+i)*stride+column)) else 0) := by
  induction count generalizing first remaining pointers with
  | zero => rfl
  | succ count ih =>
    rw [scheduledRows, List.map_append, List.map_map,
      ih (first+7) (remaining-7) _ counted.next (groupPointers_live input zero stride first remaining pointers ptrs)]
    have size : 7*(count+1) = 7+7*count := by omega
    rw [size, List.range_add, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro i hi
      exact selectedRow_original m input zero stride first column remaining pointers counted.positive zeros ptrs i
        (List.mem_range.mp hi)
    · apply List.map_congr_left
      intro i hi
      simp only [Function.comp_def]
      have test : (i : Int) < remaining-7 ↔ ((7+i : Nat) : Int) < remaining := by omega
      simp only [test, Nat.add_assoc]

end Salty.Kernels.Rdsum
