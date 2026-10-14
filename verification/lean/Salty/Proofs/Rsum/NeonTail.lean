import Salty.Proofs.Rsum.NeonBlocks

namespace Salty.Kernels.Rsum
open CByte ReductionISA

def neonTail (kind : Interpretation) : Stmt := firstStatement (dropStatements 3 (neonPartialBody kind))
def neonTailBody (kind : Interpretation) : Stmt := branchYes (neonTail kind)
def maskedBytes (xs : List Byte) (r : Nat) : List Byte := List.zipWith (· * ·) xs (tailMask r)

def neonTailAfter (kind : Interpretation) (s : State) (r : Nat) (acc : List (BitVec 16)) (xs : List Byte) : State :=
  let t := update s "vt_2" (.vector 1 xs)
  let t := update t "vonemask" (.vector 1 (tailMask r))
  let t := update t "vtm" (.vector 1 (maskedBytes xs r))
  update t "vacc16" (.halfwords (pairAcc16 kind acc (maskedBytes xs r)))

theorem tailMask_length (r : Nat) (hr : r ≤ 16) : (tailMask r).length = 16 := by
  rw [tailMask_eq r hr]
  simp only [List.length_append, List.length_replicate]
  omega

theorem maskedBytes_length (xs : List Byte) (r : Nat) (hx : xs.length = 16) (hr : r ≤ 16) :
    (maskedBytes xs r).length = 16 := by simp [maskedBytes, List.length_zipWith, hx, tailMask_length r hr]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem neon_tail_body_exec (cfg : Config) (kind : Interpretation) (s : State) (r : Nat) (input : Address)
    (acc : List (BitVec 16)) (xs : List Byte) (loc : BlockLocals .remainder s r input acc)
    (table : s.locals "onemask_table" = some (.vector 1 oneMaskTable))
    (hr : r < 16) (ha : acc.length = 8) (hx : xs.length = 16)
    (load : loadBytes s.memory input 16 = some xs) :
    Exec cfg (neonTailBody kind) s (neonTailAfter kind s r acc xs) := by
  have count : s.locals "batch" = some (.integer r) := loc.count
  have accumulator : s.locals "vacc16" = some (.halfwords acc) := loc.accumulator
  have diff : max (((16 : Int) - r) % 18446744073709551616) 0 = (16-r : Nat) := by
    simpa [convert] using cast_sub 16 r (by omega) (by decide)
  have maskLength := tailMask_length r (by omega)
  have maskedLength := maskedBytes_length xs r hx (by omega)
  have tableLength : oneMaskTable.length = 32 := by decide
  have inRange : 16-r+16 ≤ oneMaskTable.length := by rw [tableLength]; omega
  have maskNorm : min 16 (oneMaskTable.length - (16-r)) = 16 := by rw [tableLength]; omega
  cases kind <;> apply run_sound (fuel := 12) <;>
    simp +contextual [neonTailBody, neonTail, neonPartialBody, neonPartial, branchYes,
      neonProgram, Generated.QS8Rsum.neon, Generated.QU8Rsum.neon,
      firstStatement, dropStatements, run, eval, intrinsic, reductionIntrinsic, binary,
      convert, count, loc.inputPtr, accumulator, table, update, load, ha, hx,
      neonTailAfter, maskedBytes, zipLanes, tailMask, inRange, maskLength, maskedLength, maskNorm,
      show max (16 : Int) 0 = 16 by decide, diff]

theorem neon_tail_shape (kind : Interpretation) :
    neonTail kind = .branch (.bin .ne (.var "batch") (.cast .u64 (.lit 0))) (neonTailBody kind) .skip := by
  cases kind <;> rfl

/-- The actual padded tail has no input-pointer update. The16byte physical
load is masked with the validated table, so only r logical input bytes add to
the accumulated sum. Its16bit range needs fewer than128 prior pair updates. -/
theorem neon_tail_total (cfg : Config) (kind : Interpretation) (s : State) (r k : Nat) (input : Address)
    (acc : List (BitVec 16)) (loc : BlockLocals .remainder s r input acc)
    (table : s.locals "onemask_table" = some (.vector 1 oneMaskTable))
    (hr : r < 16) (hk : k < 128) (ha : acc.length = 8)
    (bounds : ∀ a ∈ acc, LaneBound kind k a)
    (readable : ∀ a, Footprint input (r+15) a → s.memory.readable a = true) :
    ∃ t final, Exec cfg (neonTail kind) s t ∧ t.memory = s.memory ∧
      BlockLocals .remainder t r input final ∧ final.length = 8 ∧
      sumWords (widen32 kind final) = sumWords (widen32 kind acc) +
        sumWords (widen32 kind (readBytes s.memory input r)) := by
  have count : s.locals "batch" = some (.integer r) := loc.count
  by_cases zero : r = 0
  · subst r
    refine ⟨s, acc, ?_, rfl, loc, ha, ?_⟩
    · rw [neon_tail_shape]
      apply Exec.no (v := .integer 0)
      · simp [eval, binary, convert, count]
      · rfl
      · exact .skip
    · simp [readBytes, widen32, sumWords]
  · let xs := readBytes s.memory input 16
    let final := pairAcc16 kind acc (maskedBytes xs r)
    let t := neonTailAfter kind s r acc xs
    have hx : xs.length = 16 := readBytes_length ..
    have len := maskedBytes_length xs r hx (by omega)
    have pairLen : (maskedBytes xs r).length = 2*acc.length := by rw [len, ha]
    have load : loadBytes s.memory input 16 = some xs :=
      loadBytes_success _ _ _ (fun a hp => readable a (footprint_mono (by omega) hp))
    refine ⟨t, final, ?_, rfl, ?_, (pairAcc16_length kind acc _ pairLen).trans ha, ?_⟩
    · rw [neon_tail_shape]
      apply Exec.yes (v := .integer 1)
      · simp [eval, binary, convert, count, zero]
      · rfl
      · exact neon_tail_body_exec cfg kind s r input acc xs loc table hr ha hx load
    · constructor <;> simp [t, final, neonTailAfter, update, countName, accumulatorName, count, loc.inputPtr]
    · dsimp only [final]
      rw [pairAcc16_sum kind k hk acc _ pairLen bounds]
      rw [maskedBytes, masked_tail_sum kind xs r hx (by omega)]
      rw [show xs.take r = readBytes s.memory input r from readBytes_take _ _ r 16 (by omega)]

end Salty.Kernels.Rsum
