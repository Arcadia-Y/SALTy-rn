import Salty.Proofs.Rsum.NeonPartial
import Salty.Proofs.Rsum.RvvComplete

namespace Salty.Kernels.Rsum
open CByte ReductionISA

def neonInitialized (s : State) : State :=
  update (update s "onemask_table" (.vector 1 oneMaskTable)) "vacc0" (.words32 (List.replicate 4 0))

def neonFinish (kind : Interpretation) : Stmt := dropStatements 8 (neonProgram kind)

def neonFinished (kind : Interpretation) (s : State) (acc : List (BitVec 32)) (m : Memory) : State :=
  { update s "vacc" (.integer (value kind (sumWords acc))) with memory := m }

set_option maxHeartbeats 1000000 in
theorem neon_init_exec (cfg : Config) (kind : Interpretation) (s : State) (c : Call) (h : Entry kind s c) :
    Exec cfg (takeStatements 6 (neonProgram kind)) s (neonInitialized s) := by
  have hn : c.count ≠ 0 := by have := h.positive; omega
  have hi : c.input ≠ 0#64 := h.inputNonzero
  have ho : c.output ≠ 0#64 := h.outputNonzero
  have hp : c.params ≠ 0#64 := h.paramsNonzero
  cases kind <;> apply run_sound (fuel := 16) <;>
    simp +contextual [takeStatements, neonProgram, Generated.QS8Rsum.neon, Generated.QU8Rsum.neon,
      run, eval, truth, binary, convert, effect, intrinsic, reductionIntrinsic,
      saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic, h.batch, h.inputPtr, h.outputPtr,
      h.paramsPtr, hi, ho, hp, hn, neonInitialized, update, oneMaskTable, List.replicate_succ]

theorem neonInitialized_locals (kind : Interpretation) (s : State) (c : Call) (h : Entry kind s c) :
    NeonLocals (neonInitialized s) c.count c.input c.output (List.replicate 4 0) := by
  constructor <;> simp [neonInitialized, update, h.batch, h.inputPtr, h.outputPtr]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem neon_finish_exec (cfg : Config) (kind : Interpretation) (s : State) (output : Address)
    (acc : List (BitVec 32)) (initial : BitVec 32)
    (vacc : s.locals "vacc0" = some (.words32 acc)) (out : s.locals "output" = some (.pointer output))
    (ha : acc.length = 4)
    (load : loadParam s.memory output = some (.integer initial.toInt))
    (defined : OutputDefined kind initial (sumWords acc))
    (writable : ∀ a, Footprint output 4 a → s.memory.writable a = true) :
    Exec cfg (neonFinish kind) s (neonFinished kind s acc
      (writeBytes s.memory output (bytes32 (outputScalar kind initial (sumWords acc))))) := by
  have store : storeBytes s.memory output (bytes32 (outputScalar kind initial (sumWords acc))) =
      some (writeBytes s.memory output (bytes32 (outputScalar kind initial (sumWords acc)))) := by
    apply storeBytes_success
    simpa [bytes32] using writable
  cases kind with
  | signed =>
    simp only [outputScalar] at store
    have defn := defined
    change -2147483648 ≤ initial.toInt + (sumWords acc).toInt ∧ initial.toInt + (sumWords acc).toInt < 2147483648 at defn
    apply run_sound (fuel := 8)
    simp +contextual [neonFinish, neonProgram, Generated.QS8Rsum.neon, dropStatements,
      run, eval, intrinsic, reductionIntrinsic, effect, binary, update, neonFinished,
      vacc, out, ha, load, defn, value, outputScalar, store]
  | unsigned =>
    simp only [outputScalar] at store
    have defn := outputScalar_unsigned_bounds initial (sumWords acc)
    simp [outputScalar] at defn
    simp at store
    have repr : max (initial.toInt % 4294967296) 0 = (initial.toNat : Int) := by
      have h := congrArg (fun x : BitVec 32 => (x.toNat : Int)) (BitVec.ofInt_toInt (x := initial))
      simpa only [BitVec.toNat_ofInt, Int.ofNat_toNat, Nat.reducePow, Int.reduceNatCast] using h
    apply run_sound (fuel := 8)
    simp +contextual [neonFinish, neonProgram, Generated.QU8Rsum.neon, dropStatements,
      run, eval, intrinsic, reductionIntrinsic, effect, binary, update, neonFinished,
      vacc, out, ha, load, defn, value, outputScalar, convert, store, repr]

/-- Complete source execution, with unbounded outer and inner loops, padded
masked tail, horizontal reduction, and the actual final scalar update. -/
theorem neon_correct (cfg : Config) (kind : Interpretation) (s : State) (c : Call)
    (h : Entry kind s c) :
    ∃ t, Exec cfg (neonProgram kind) s t ∧ t.memory = resultMemory kind s.memory c := by
  let start := neonInitialized s
  have init : Exec cfg (takeStatements 6 (neonProgram kind)) s start := neon_init_exec cfg kind s c h
  have loc := neonInitialized_locals kind s c h
  have read : ∀ a, Footprint c.input c.count a → start.memory.readable a = true :=
    fun a ha => h.readable a (footprint_mono (by omega) ha)
  obtain ⟨u, r, acc, outer, outerMem, outerLoc, small, le, length, outerSum⟩ :=
    neon_outer_total cfg kind start c.count c.input c.output (List.replicate 4 0)
      loc h.size (by simp) read
  have uMem : u.memory = s.memory := outerMem
  have remainderRead : ∀ a, Footprint (c.input+BitVec.ofNat 64 (c.count-r)) (r+15) a → u.memory.readable a = true := by
    intro a ha
    rw [uMem]
    exact h.readable a (footprint_shift_within (by omega) ha)
  obtain ⟨v, finalAcc, remainder, remainderMem, vacc, out, finalLength, remainderSum⟩ :=
    neon_partial_total cfg kind u r (c.input+BitVec.ofNat 64 (c.count-r)) c.output acc
      outerLoc small length remainderRead
  have vMem : v.memory = s.memory := remainderMem.trans uMem
  have total : sumWords finalAcc = byteSum kind s.memory c.input c.count := by
    rw [remainderSum, uMem, outerSum]
    have joined := readBytes_add s.memory c.input (c.count-r) r
    have count : c.count-r+r = c.count := by omega
    rw [count] at joined
    change _ = sumWords (widen32 kind (readBytes s.memory c.input c.count))
    rw [joined]
    simp only [widen32, List.map_append, sumWords_append]
    rw [show sumWords (List.replicate 4 (0 : BitVec 32)) = 0#32 by decide, BitVec.zero_add]
    rfl
  have load : loadParam v.memory c.output = some (.integer c.initial.toInt) := by
    rw [vMem]; exact h.initialLoad
  have defined : OutputDefined kind c.initial (sumWords finalAcc) := by rw [total]; exact h.defined
  have writable : ∀ a, Footprint c.output 4 a → v.memory.writable a = true := by
    rw [vMem]; exact h.writable
  have finish := neon_finish_exec cfg kind v c.output finalAcc c.initial vacc out finalLength load defined writable
  rw [vMem, total] at finish
  let final := neonFinished kind v finalAcc (resultMemory kind s.memory c)
  have finished : Exec cfg (neonFinish kind) v final := finish
  refine ⟨final, ?_, rfl⟩
  have rest : Exec cfg (.seq (neonOuter kind) (.seq (neonPartial kind) (neonFinish kind))) start final :=
    .seq outer (.seq remainder finished)
  have shape : dropStatements 6 (neonProgram kind) = .seq (neonOuter kind) (.seq (neonPartial kind) (neonFinish kind)) := by
    cases kind <;> rfl
  rw [← shape] at rest
  exact exec_take_drop 6 init rest

end Salty.Kernels.Rsum
