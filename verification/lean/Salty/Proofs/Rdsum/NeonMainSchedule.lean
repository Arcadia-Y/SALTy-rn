import Salty.Proofs.Rdsum.NeonMainInner

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

theorem selectedPointers_shift (pointers : Nat → Address) (remaining : Int) (zero offset : Address) :
    selectedPointers (fun i => pointers i+offset) remaining (zero+offset) =
      fun i => selectedPointers pointers remaining zero i+offset := by
  funext i
  unfold selectedPointers
  split <;> rfl

theorem groupPointers_shift (pointers : Nat → Address) (remaining : Int) (zero offset : Address) (increment : Nat) :
    groupPointers (fun i => pointers i+offset) (zero+offset) remaining increment =
      fun i => groupPointers pointers zero remaining increment i+offset := by
  funext i
  simp only [groupPointers, selectedPointers_shift]
  ac_rfl

theorem mainRowsAcc_groupRows (kind : Interpretation) (m : Memory) (pointers : Nat → Address)
    (zero : Address) (remaining : Int) (initial : Nat → List (BitVec 16)) (chunk : Nat) :
    rowAcc kind (groupRows m (fun i => pointers i+BitVec.ofNat 64 (8*chunk))
      (zero+BitVec.ofNat 64 (8*chunk)) remaining 8) (initial chunk) 7 =
      mainRowsAcc kind m (selectedPointers pointers remaining zero) initial 7 chunk := by
  unfold groupRows mainRowsAcc
  rw [selectedPointers_shift]

/-- Each independent main-path chunk is exactly the already verified seven-row
schedule at an eight-byte column offset, including substituted zero pointers. -/
theorem mainFold_chunk (kind : Interpretation) (m : Memory) (zero : Address) (increment count : Nat)
    (pointers : Nat → Address) (remaining : Int) (initial : Nat → List (BitVec 16)) (chunk : Nat) :
    groupFold kind m (zero+BitVec.ofNat 64 (8*chunk)) 8 increment count
      (fun i => pointers i+BitVec.ofNat 64 (8*chunk)) remaining (initial chunk) =
      let result := mainFold kind m zero increment count pointers remaining initial
      ⟨(fun i => result.pointers i+BitVec.ofNat 64 (8*chunk)),result.remaining,result.acc chunk⟩ := by
  induction count generalizing pointers remaining initial with
  | zero => rfl
  | succ count ih =>
    simp only [groupFold, mainFold, groupPointers_shift, mainRowsAcc_groupRows]
    exact ih _ _ _

end Salty.Kernels.Rdsum
