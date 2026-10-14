import Salty.Proofs.Rsum.NeonOuter
import Salty.Proofs.Rsum.NeonTail

namespace Salty.Kernels.Rsum
open CByte ReductionISA

set_option maxHeartbeats 1000000 in
theorem partial_init_exec (cfg : Config) (kind : Interpretation) (s : State) (n : Nat)
    (count : s.locals "batch" = some (.integer n)) (positive : 0 < n) (small : n < 2048) :
    Exec cfg (takeStatements 2 (neonPartialBody kind)) s
      (update s "vacc16" (.halfwords (List.replicate 8 0))) := by
  have lo : (1 : Int) ≤ n := by omega
  have hi : (n : Int) < 2048 := by omega
  cases kind <;> apply run_sound (fuel := 8) <;>
    simp [neonPartialBody, neonPartial, neonProgram, branchYes, Generated.QS8Rsum.neon, Generated.QU8Rsum.neon,
      takeStatements, firstStatement, dropStatements, run, eval, binary, convert, truth, effect, intrinsic,
      saturatingIntrinsic, count, lo, hi, Int.max_def]

theorem partial_rest_shape (kind : Interpretation) :
    dropStatements 2 (neonPartialBody kind) = .seq (neonBlockLoop kind .remainder)
      (.seq (neonTail kind) (.seq (.assign "vacc0" (.call (pair32Prim kind) [.var "vacc0", .var "vacc16"])) .skip)) := by
  cases kind <;> rfl

theorem neon_partial_shape (kind : Interpretation) :
    neonPartial kind = .branch (.bin .ne (.var "batch") (.cast .u64 (.lit 0))) (neonPartialBody kind) .skip := by
  cases kind <;> rfl

set_option maxRecDepth 4096 in
theorem neon_partial_total (cfg : Config) (kind : Interpretation) (s : State) (n : Nat)
    (input output : Address) (acc : List (BitVec 32)) (loc : NeonLocals s n input output acc)
    (small : n < 2048) (length : acc.length = 4)
    (readable : ∀ a, Footprint input (n+15) a → s.memory.readable a = true) :
    ∃ t final, Exec cfg (neonPartial kind) s t ∧ t.memory = s.memory ∧
      t.locals "vacc0" = some (.words32 final) ∧ t.locals "output" = some (.pointer output) ∧
      final.length = 4 ∧ sumWords final = sumWords acc + sumWords (widen32 kind (readBytes s.memory input n)) := by
  by_cases zero : n = 0
  · subst n
    refine ⟨s, acc, ?_, rfl, loc.accumulator, loc.outputPtr, length, ?_⟩
    · rw [neon_partial_shape]
      apply Exec.no (v := .integer 0)
      · simp [eval, binary, convert, loc.batch]
      · rfl
      · exact .skip
    · simp [readBytes, widen32, sumWords]
  · let q := n / 16
    let r := n % 16
    have split : 16*q+r = n := by dsimp [q, r]; omega
    have hr : r < 16 := by dsimp [r]; omega
    have hq : q < 128 := by dsimp [q]; omega
    let start := update s "vacc16" (.halfwords (List.replicate 8 0))
    have init : Exec cfg (takeStatements 2 (neonPartialBody kind)) s start :=
      partial_init_exec cfg kind s n loc.batch (by omega) small
    have blockLoc : BlockLocals .remainder start (16*q+r) input (List.replicate 8 0) := by
      constructor <;> simp [start, update, countName, accumulatorName, loc.batch, loc.inputPtr, split]
    have bounds : ∀ a ∈ (List.replicate 8 (0 : BitVec 16)), LaneBound kind 0 a := by
      intro a ha
      have eq : a = 0 := by simpa using ha
      rw [eq]
      exact laneBound_zero kind
    have blockRead : ∀ a, Footprint input (16*q) a → start.memory.readable a = true :=
      fun a ha => readable a (footprint_mono (by omega) ha)
    obtain ⟨u, narrow, loop, loopMem, loopLoc, narrowLength, narrowBounds, loopSum⟩ :=
      neon_block_loop_total cfg kind .remainder q r 0 start input (List.replicate 8 0)
        blockLoc hr (by intro h; cases h) (by omega) (by simp) bounds (by omega) blockRead
    have uMem : u.memory = s.memory := loopMem
    have uTable : u.locals "onemask_table" = some (.vector 1 oneMaskTable) := by
      rw [loop.locals_frame "onemask_table" (by cases kind <;> rfl)]
      simp [start, update, loc.table]
    have tailRead : ∀ a, Footprint (input+BitVec.ofNat 64 (16*q)) (r+15) a → u.memory.readable a = true := by
      intro a ha
      rw [uMem]
      exact readable a (footprint_shift_within (by omega) ha)
    obtain ⟨v, final16, tail, tailMem, tailLoc, final16Length, tailSum⟩ :=
      neon_tail_total cfg kind u r q (input+BitVec.ofNat 64 (16*q)) narrow loopLoc uTable hr hq narrowLength
        (by simpa using narrowBounds) tailRead
    have vMem : v.memory = s.memory := tailMem.trans uMem
    have vAcc : v.locals "vacc0" = some (.words32 acc) := by
      rw [tail.locals_frame "vacc0" (by cases kind <;> rfl), loop.locals_frame "vacc0" (by cases kind <;> rfl)]
      simp [start, update, loc.accumulator]
    have vOutput : v.locals "output" = some (.pointer output) := by
      rw [tail.locals_frame "output" (by cases kind <;> rfl), loop.locals_frame "output" (by cases kind <;> rfl)]
      simp [start, update, loc.outputPtr]
    let final := pairAcc32 kind acc final16
    let t := update v "vacc0" (.words32 final)
    have widen : Exec cfg (.assign "vacc0" (.call (pair32Prim kind) [.var "vacc0", .var "vacc16"])) v t := by
      apply Exec.assign
      have half : v.locals "vacc16" = some (.halfwords final16) := tailLoc.accumulator
      simpa only [eval, vAcc, half, List.mapM_cons, List.mapM_nil, Option.bind_some, pure, Option.pure_def]
        using pair32_intrinsic cfg v.memory kind acc final16 length final16Length
    have rest : Exec cfg (dropStatements 2 (neonPartialBody kind)) start t := by
      rw [partial_rest_shape]
      exact .seq loop (.seq tail (.seq widen .skip))
    refine ⟨t, final, ?_, vMem, by simp [t, update], by simp [t, update, vOutput], ?_, ?_⟩
    · rw [neon_partial_shape]
      apply Exec.yes (v := .integer 1)
      · simp [eval, binary, convert, loc.batch, zero]
      · rfl
      · exact exec_take_drop 2 init rest
    · exact (pairAcc32_length kind acc final16 (by rw [final16Length, length])).trans length
    · dsimp only [final]
      rw [pairAcc32_sum kind acc final16 (by rw [final16Length, length]), tailSum, uMem]
      have zeroSum : sumWords (widen32 kind (List.replicate 8 (0 : BitVec 16))) = 0 := sum_widen_zero kind 8
      rw [zeroSum] at loopSum
      have prefixSum : sumWords (widen32 kind narrow) = sumWords (widen32 kind (readBytes s.memory input (16*q))) := by
        simpa using loopSum
      rw [prefixSum]
      have joined := readBytes_add s.memory input (16*q) r
      rw [split] at joined
      rw [joined]
      simp only [widen32, List.map_append, sumWords_append]

end Salty.Kernels.Rsum
