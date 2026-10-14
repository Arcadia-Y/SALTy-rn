import Salty.Proofs.Rdsum.RvvPointers

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def selectedPointers (pointers : Nat → Address) (remaining : Int) (zero : Address) (i : Nat) : Address :=
  if 0 < i ∧ remaining ≤ (i : Int) then zero else pointers i

/-- One actual seven-row body, before the for-loop decrement. The signed RVV
body loads all seven rows before its adds; the unsigned body interleaves them.
Both produce the same sequential widened row sum without changing memory. -/
theorem rvv_group_exec (kind : Interpretation) (cfg : Config) (s : State)
    (pointers : Nat → Address) (zero : Address) (remaining : Int) (n increment : Nat)
    (acc : List (BitVec 16)) (cap : n ≤ cfg.capacity) (ha : acc.length = n)
    (ptr : ∀ i, i < 7 → s.locals (rowName i) = some (.pointer (pointers i)))
    (vl : s.locals "vl" = some (.integer n))
    (vacc : s.locals "vacc16" = some (.halfwords acc))
    (hz : s.locals "zero" = some (.pointer zero))
    (hr : s.locals "current_batch" = some (.integer remaining))
    (step : s.locals "input_increment" = some (.integer increment))
    (safe : ∀ i, i < 7 → ∀ a,
      Footprint (selectedPointers pointers remaining zero i) n a → s.memory.readable a = true) :
    ∃ t, Exec cfg (rvvGroup kind) s t ∧ t.memory = s.memory ∧
      t.locals "vacc16" = some (.halfwords (rowAcc kind
        (fun i => readBytes s.memory (selectedPointers pointers remaining zero i) n) acc 7)) ∧
      (∀ i, i < 7 → t.locals (rowName i) =
        some (.pointer (selectedPointers pointers remaining zero i+BitVec.ofNat 64 increment))) := by
  let chosen := selectedPointers pointers remaining zero
  let z := zerosAfter s remaining zero
  have zeroExec : Exec cfg zeroBranches s z := zeros_exec cfg s remaining zero hr hz
  have zeroMem : z.memory = s.memory := zerosAfter_memory ..
  have zeroPtrs : ∀ i, i < 7 → z.locals (rowName i) = some (.pointer (chosen i)) := by
    intro i hi
    rw [zerosAfter_row s remaining zero i hi, ptr i hi]
    simp only [chosen, selectedPointers]
    split <;> rfl
  have zeroVl : z.locals "vl" = some (.integer n) :=
    (zeroExec.locals_frame "vl" (by rfl)).trans vl
  have zeroAcc : z.locals "vacc16" = some (.halfwords acc) :=
    (zeroExec.locals_frame "vacc16" (by rfl)).trans vacc
  let rows := fun i => readBytes s.memory (chosen i) n
  let d := rvvDataAfter kind z rows acc
  have dataExec : Exec cfg (rvvData kind) z d := by
    have h := rvv_data_exec kind cfg z chosen n acc cap ha zeroPtrs zeroVl zeroAcc
      (by simpa only [zeroMem] using safe)
    simpa only [zeroMem] using h
  have dataMem : d.memory = s.memory := (rvvDataAfter_memory ..).trans zeroMem
  have dataPtrs : ∀ i, i < 7 → d.locals (rowName i) = some (.pointer (chosen i)) := by
    intro i hi
    exact (rvvDataAfter_row kind z rows acc i hi).trans (zeroPtrs i hi)
  have dataStep : d.locals "input_increment" = some (.integer increment) :=
    (dataExec.locals_frame "input_increment" (by cases kind <;> rfl)).trans
      ((zeroExec.locals_frame "input_increment" (by rfl)).trans step)
  let t := pointersAfter d chosen increment
  have pointerExec : Exec cfg (rvvIncrements kind) d t :=
    rvv_increments_exec kind cfg d chosen increment dataPtrs dataStep
  refine ⟨t, ?_, (pointersAfter_memory ..).trans dataMem, ?_, ?_⟩
  · apply exec_take_drop 6
    · rw [rvv_zero_shape]; exact zeroExec
    · apply exec_take_drop 14 dataExec
      cases kind <;> exact pointerExec
  · exact (pointerExec.locals_frame "vacc16" (by cases kind <;> rfl)).trans
      (rvvDataAfter_acc kind z rows acc)
  · intro i hi
    exact pointersAfter_row d chosen increment i hi

/-- The actual loop body includes a checked signed decrement after pointer
advances; positive partial groups may finish at a negative remainder. -/
def rvvIteration (kind : Interpretation) : Stmt :=
  match kind with
  | .signed => loopBody (firstStatement (dropStatements 1
      (firstStatement (dropStatements 1 (rvvBatches kind)))))
  | .unsigned => loopBody (firstStatement (dropStatements 3 (rvvBatches kind)))

theorem rvv_iteration_shape (kind : Interpretation) : rvvIteration kind =
    .seq (rvvGroup kind) (.assign "current_batch"
      (.checkedSigned32 (.bin .sub (.var "current_batch") (.lit 7)))) := by
  cases kind <;> rfl

end Salty.Kernels.Rdsum
