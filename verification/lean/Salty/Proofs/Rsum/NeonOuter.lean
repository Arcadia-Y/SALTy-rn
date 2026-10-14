import Salty.Proofs.Rsum.NeonBlocks

set_option maxRecDepth 4096
namespace Salty.Kernels.Rsum
open CByte ReductionISA

structure NeonLocals (s : State) (n : Nat) (input output : Address) (acc : List (BitVec 32)) : Prop where
  batch : s.locals "batch" = some (.integer n)
  inputPtr : s.locals "input" = some (.pointer input)
  outputPtr : s.locals "output" = some (.pointer output)
  accumulator : s.locals "vacc0" = some (.words32 acc)
  table : s.locals "onemask_table" = some (.vector 1 oneMaskTable)

def halfZeroExpr (kind : Interpretation) : Expr :=
  .call .dupI16x8 [.cast (match kind with | .signed => .i16 | .unsigned => .u16) (.lit 0)]

def outerStart (s : State) : State :=
  update (update s "vacc16_0" (.halfwords (List.replicate 8 0))) "current_batch" (.integer 2048)

def outerFinish (s : State) (n : Nat) (acc : List (BitVec 32)) : State :=
  update (update s "vacc0" (.words32 acc)) "batch" (.integer (n-2048 : Nat))

theorem neon_outer_body_shape (kind : Interpretation) :
    neonOuterBody kind =
      .seq (.seq (.assign "vacc16_0" (halfZeroExpr kind))
        (.seq (.seq (.assign "current_batch" (.cast .u64 (.lit 2048))) (neonBlockLoop kind .full))
          (.seq (.assign "vacc0" (.call (pair32Prim kind) [.var "vacc0", .var "vacc16_0"])) .skip)))
        (.assign "batch" (.cast .u64 (.bin .sub (.var "batch") (.cast .u64 (.lit 2048))))) := by
  cases kind <;> rfl

theorem zero_half_eval (cfg : Config) (kind : Interpretation) (s : State) :
    eval cfg s (halfZeroExpr kind) = some (.halfwords (List.replicate 8 0)) := by
  cases kind <;> simp [halfZeroExpr, eval, intrinsic, saturatingIntrinsic, convert]

/-- One complete 2048-byte source iteration: exactly 128 pair accumulations,
then a widened modular 32-bit update. The local 16-bit range never overflows. -/
theorem neon_outer_body_exec (cfg : Config) (kind : Interpretation) (s : State) (n : Nat)
    (input output : Address) (acc : List (BitVec 32)) (loc : NeonLocals s n input output acc)
    (size : n < 2^64) (enough : 2048 ≤ n) (length : acc.length = 4)
    (readable : ∀ a, Footprint input 2048 a → s.memory.readable a = true) :
    ∃ t final, Exec cfg (neonOuterBody kind) s t ∧ t.memory = s.memory ∧
      NeonLocals t (n-2048) (input+2048) output final ∧ final.length = 4 ∧
      sumWords final = sumWords acc + sumWords (widen32 kind (readBytes s.memory input 2048)) := by
  let start := outerStart s
  have init16 : Exec cfg (.assign "vacc16_0" (halfZeroExpr kind)) s
      (update s "vacc16_0" (.halfwords (List.replicate 8 0))) := .assign (zero_half_eval cfg kind s)
  have initCount : Exec cfg (.assign "current_batch" (.cast .u64 (.lit 2048)))
      (update s "vacc16_0" (.halfwords (List.replicate 8 0))) start := by
    apply Exec.assign
    simp [eval, convert]
    rfl
  have blockLoc : BlockLocals .full start (16*128+0) input (List.replicate 8 0) := by
    constructor <;> simp [start, outerStart, update, countName, accumulatorName, loc.inputPtr]
  have bounds : ∀ a ∈ (List.replicate 8 (0 : BitVec 16)), LaneBound kind 0 a := by
    intro a ha
    have eq : a = 0 := by simpa using ha
    rw [eq]
    exact laneBound_zero kind
  obtain ⟨u, narrow, inner, mem, innerLoc, narrowLength, _, total⟩ :=
    neon_block_loop_total cfg kind .full 128 0 0 start input (List.replicate 8 0)
      blockLoc (by decide) (by intro; rfl) (by decide) (by simp) bounds (by decide) readable
  have accLocal : u.locals "vacc0" = some (.words32 acc) := by
    rw [inner.locals_frame "vacc0" (by cases kind <;> rfl)]
    simp [start, outerStart, update, loc.accumulator]
  have countLocal : u.locals "batch" = some (.integer n) := by
    rw [inner.locals_frame "batch" (by cases kind <;> rfl)]
    simp [start, outerStart, update, loc.batch]
  have outputLocal : u.locals "output" = some (.pointer output) := by
    rw [inner.locals_frame "output" (by cases kind <;> rfl)]
    simp [start, outerStart, update, loc.outputPtr]
  have tableLocal : u.locals "onemask_table" = some (.vector 1 oneMaskTable) := by
    rw [inner.locals_frame "onemask_table" (by cases kind <;> rfl)]
    simp [start, outerStart, update, loc.table]
  let final := pairAcc32 kind acc narrow
  let t := outerFinish u n final
  have widen : Exec cfg (.assign "vacc0" (.call (pair32Prim kind) [.var "vacc0", .var "vacc16_0"]))
      u (update u "vacc0" (.words32 final)) := by
    apply Exec.assign
    have narrowLocal : u.locals "vacc16_0" = some (.halfwords narrow) := innerLoc.accumulator
    simpa only [eval, accLocal, narrowLocal, List.mapM_cons, List.mapM_nil, Option.bind_some,
      pure, Option.pure_def] using pair32_intrinsic cfg u.memory kind acc narrow length narrowLength
  have sub : max (((n : Int)-2048) % 18446744073709551616) 0 = (n-2048 : Nat) := by
    simpa [convert] using cast_sub n 2048 enough size
  have decrement : Exec cfg (.assign "batch" (.cast .u64 (.bin .sub (.var "batch") (.cast .u64 (.lit 2048)))))
      (update u "vacc0" (.words32 final)) t := by
    apply Exec.assign
    simp [eval, binary, convert, update, countLocal, show max (2048 : Int) 0 = 2048 by decide, sub]
  refine ⟨t, final, ?_, mem, ?_, ?_, ?_⟩
  · rw [neon_outer_body_shape]
    exact .seq (.seq init16 (.seq (.seq initCount inner) (.seq widen .skip))) decrement
  · constructor <;> simp [t, outerFinish, update, outputLocal, tableLocal]
    simpa using innerLoc.inputPtr
  · exact (pairAcc32_length kind acc narrow (by rw [narrowLength, length])).trans length
  · dsimp only [final]
    rw [pairAcc32_sum kind acc narrow (by rw [narrowLength, length])]
    have zero : sumWords (widen32 kind (List.replicate 8 (0 : BitVec 16))) = 0 := sum_widen_zero kind 8
    rw [zero] at total
    simpa using congrArg (fun x => sumWords acc + x) total

theorem neon_outer_shape (kind : Interpretation) :
    neonOuter kind = .loop (.bin .ge (.var "batch") (.cast .u64 (.lit 2048))) (neonOuterBody kind) := by
  cases kind <;> rfl

/-- Unbounded outer source loop. It leaves fewer than 2048 logical input bytes
for the remainder block and preserves every memory byte and permission. -/
theorem neon_outer_total (cfg : Config) (kind : Interpretation) (s : State) (n : Nat)
    (input output : Address) (acc : List (BitVec 32)) (loc : NeonLocals s n input output acc)
    (size : n < 2^64) (length : acc.length = 4)
    (readable : ∀ a, Footprint input n a → s.memory.readable a = true) :
    ∃ t r final, Exec cfg (neonOuter kind) s t ∧ t.memory = s.memory ∧
      NeonLocals t r (input + BitVec.ofNat 64 (n-r)) output final ∧ r < 2048 ∧ r ≤ n ∧ final.length = 4 ∧
      sumWords final = sumWords acc + sumWords (widen32 kind (readBytes s.memory input (n-r))) := by
  induction n using Nat.strongRecOn generalizing s input acc with
  | ind n ih =>
    by_cases enough : 2048 ≤ n
    · obtain ⟨next, nextAcc, body, memory, nextLoc, nextLength, nextSum⟩ :=
        neon_outer_body_exec cfg kind s n input output acc loc size enough length
          (fun a ha => readable a (footprint_mono enough ha))
      have nextRead : ∀ a, Footprint (input+2048) (n-2048) a → next.memory.readable a = true := by
        intro a ha
        rw [memory]
        exact readable a (footprint_shift_within (start := 2048) (by omega) ha)
      obtain ⟨t, r, final, execution, memFinal, finalLoc, small, le, finalLength, total⟩ :=
        ih (n-2048) (by omega) next (input+2048) nextAcc nextLoc (by omega) nextLength nextRead
      refine ⟨t, r, final, ?_, memFinal.trans memory, ?_, small, by omega, finalLength, ?_⟩
      · rw [neon_outer_shape] at execution ⊢
        apply Exec.more (v := .integer 1) (t := next)
        · simp [eval, binary, convert, loc.batch, show max (2048 : Int) 0 = 2048 by decide,
            show (2048 : Int) ≤ n by omega]
        · rfl
        · exact body
        · exact execution
      · have address : input+2048+BitVec.ofNat 64 (n-2048-r) = input+BitVec.ofNat 64 (n-r) := by
          change input + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (n-2048-r) = _
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          congr 2
          omega
        rw [address] at finalLoc
        exact finalLoc
      · rw [total, memory, nextSum]
        have joined := readBytes_add s.memory input 2048 (n-2048-r)
        have count : 2048+(n-2048-r) = n-r := by omega
        rw [count] at joined
        rw [joined]
        simp only [widen32, List.map_append, sumWords_append, BitVec.add_assoc]
        rfl
    · refine ⟨s, n, acc, ?_, rfl, ?_, by omega, Nat.le_refl _, length, ?_⟩
      · rw [neon_outer_shape]
        apply Exec.done (v := .integer 0)
        · simp [eval, binary, convert, loc.batch, show max (2048 : Int) 0 = 2048 by decide,
            show ¬ (2048 : Int) ≤ n by omega]
        · rfl
      · simpa using loc
      · simp [readBytes, widen32, sumWords]

end Salty.Kernels.Rsum
