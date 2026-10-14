import Salty.Proofs.Rdsum.RvvBatch
import Salty.Proofs.Rdsum.Memory

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- Memory geometry for a fixed column strip throughout a bounded row batch.
Only live row pointers are constrained; dead rows are redirected before reads. -/
theorem groups_safe_of_rows (m : Memory) (input zero : Address) (stride width total count : Nat)
    (rows : ∀ row, row < total → ∀ a,
      Footprint (input+BitVec.ofNat 64 (row*stride)) width a → m.readable a = true)
    (zeros : ∀ a, Footprint zero width a → m.readable a = true)
    (first : Nat) (remaining : Int) (pointers : Nat → Address)
    (counted : GroupCount count remaining) (within : (first : Int)+remaining ≤ total)
    (ptrs : ∀ (i : Nat), i < 7 → (i : Int) < remaining →
      pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    GroupsSafe m zero width (7*stride) count pointers remaining := by
  induction count generalizing first remaining pointers with
  | zero => trivial
  | succ count ih =>
    have positive := counted.positive
    constructor
    · intro i hi a ha
      by_cases absent : 0 < i ∧ remaining ≤ (i : Int)
      · rw [selectedPointers, if_pos absent] at ha
        exact zeros a ha
      · have live : (i : Int) < remaining := by omega
        rw [selectedPointers, if_neg absent, ptrs i hi live] at ha
        exact rows (first+i) (by omega) a ha
    · apply ih (first+7) (remaining-7) (groupPointers pointers zero remaining (7*stride))
        counted.next (by omega)
      intro i hi live
      have current : (i : Int) < remaining := by omega
      have absent : ¬ (0 < i ∧ remaining ≤ (i : Int)) := by omega
      simp only [groupPointers, selectedPointers, if_neg absent, ptrs i hi current]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      simp only [Nat.add_mul]
      omega

/-- Entry provides the recursive inner-loop read-safety predicate for any
in-bounds channel strip and any interval of actual rows. -/
theorem Entry.groups_safe {kind : Interpretation} {s : State} {c : Call}
    (h : Entry kind s c) (column width first count : Nat) (remaining : Int)
    (pointers : Nat → Address) (columns : column+width ≤ c.channels)
    (counted : GroupCount count remaining) (within : (first : Int)+remaining ≤ c.rows)
    (ptrs : ∀ (i : Nat), i < 7 → (i : Int) < remaining →
      pointers i = c.input+BitVec.ofNat 64 ((first+i)*c.stride+column)) :
    GroupsSafe s.memory c.zero width (7*c.stride) count pointers remaining := by
  apply groups_safe_of_rows s.memory (c.input+BitVec.ofNat 64 column) c.zero c.stride width c.rows count
  · intro row hr a ha
    apply h.inputReadable row hr a
    apply footprint_shift_within (start := column) (count := width) (by omega)
    have eq : c.input+BitVec.ofNat 64 column+BitVec.ofNat 64 (row*c.stride) =
        c.input+BitVec.ofNat 64 (row*c.stride)+BitVec.ofNat 64 column := by ac_rfl
    simpa only [eq] using ha
  · intro a ha
    exact h.zeroReadable a (footprint_mono (by omega) ha)
  · exact counted
  · exact within
  · intro i hi live
    rw [ptrs i hi live]
    simp only [BitVec.ofNat_add]
    ac_rfl

end Salty.Kernels.Rdsum
