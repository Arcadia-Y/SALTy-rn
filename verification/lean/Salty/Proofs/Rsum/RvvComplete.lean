import Salty.Proofs.Rsum.Rvv
import Salty.Proofs.Rsum.SpecLemmas

namespace Salty.Kernels.Rsum
open CByte ReductionISA

def rvvInitialized (s : State) (capacity : Nat) : State :=
  update (update s "vlmax" (.integer capacity)) "vacc" (.words32 (List.replicate capacity 0))

def rvvFinish (kind : Interpretation) : Stmt := dropStatements 7 (rvvProgram kind)

def rvvFinished (kind : Interpretation) (s : State) (acc : List (BitVec 32)) (m : Memory) : State :=
  { update s (match kind with | .signed => "vres" | .unsigned => "red") (.words32 [sumWords acc]) with memory := m }

set_option maxHeartbeats 1000000 in
theorem rvv_init_exec (cfg : Config) (kind : Interpretation) (s : State) (c : Call) (h : Entry kind s c) :
    Exec cfg (takeStatements 6 (rvvProgram kind)) s (rvvInitialized s cfg.capacity) := by
  have hn : c.count ≠ 0 := by have := h.positive; omega
  have hi : c.input ≠ 0#64 := h.inputNonzero
  have ho : c.output ≠ 0#64 := h.outputNonzero
  have hp : c.params ≠ 0#64 := h.paramsNonzero
  cases kind <;> apply run_sound (fuel := 16) <;>
    simp +contextual [takeStatements, rvvProgram, Generated.QS8Rsum.rvv, Generated.QU8Rsum.rvv,
      run, eval, truth, binary, convert, effect, intrinsic, reductionIntrinsic,
      saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic, h.batch, h.inputPtr, h.outputPtr,
      h.paramsPtr, h.inputNonzero, h.outputNonzero, h.paramsNonzero, hi, ho, hp, hn, rvvInitialized, update]

theorem rvvInitialized_locals (cfg : Config) (kind : Interpretation) (s : State) (c : Call) (h : Entry kind s c) :
    RvvLocals (rvvInitialized s cfg.capacity) c.count c.input c.output cfg.capacity (List.replicate cfg.capacity 0) := by
  constructor <;> simp [rvvInitialized, update, h.batch, h.inputPtr, h.outputPtr]

theorem head_replicate_zero (n : Nat) (hn : 0 < n) :
    (List.replicate n (0 : BitVec 32)).head! = 0 := by
  cases n with
  | zero => omega
  | succ n => rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem rvv_finish_exec (cfg : Config) (kind : Interpretation) (s : State) (input output : Address)
    (acc : List (BitVec 32)) (initial : BitVec 32)
    (loc : RvvLocals s 0 input output cfg.capacity acc) (ha : acc.length = cfg.capacity)
    (cap : 8 ≤ cfg.capacity)
    (load : loadParam s.memory output = some (.integer initial.toInt))
    (defined : OutputDefined kind initial (sumWords acc))
    (writable : ∀ a, Footprint output 4 a → s.memory.writable a = true) :
    Exec cfg (rvvFinish kind) s (rvvFinished kind s acc
      (writeBytes s.memory output (bytes32 (outputScalar kind initial (sumWords acc))))) := by
  have positive : 0 < cfg.capacity := by omega
  have seedPos : 0 < cfg.capacity / 8 := Nat.div_pos cap (by decide)
  have takeAcc : acc.take cfg.capacity = acc := List.take_of_length_le (by omega)
  have seedNonneg : (0 : Int) ≤ (cfg.capacity : Int) / 8 := by omega
  have seedIntPos : (0 : Int) < (cfg.capacity : Int) / 8 := by omega
  have seedNat : ((cfg.capacity : Int) / 8).toNat = cfg.capacity / 8 := by omega
  have headZero : (List.replicate ((cfg.capacity : Int) / 8).toNat (0#32)).head! = 0#32 := by
    rw [seedNat]
    exact head_replicate_zero _ seedPos
  have headSingle (x : BitVec 32) : ([x] : List (BitVec 32)).head! = x := rfl
  have oldHeadZero : (List.replicate (cfg.capacity / 8) (0#32)).head! = 0#32 :=
    head_replicate_zero (cfg.capacity / 8) seedPos
  have store : storeBytes s.memory output (bytes32 (outputScalar kind initial (sumWords acc))) =
      some (writeBytes s.memory output (bytes32 (outputScalar kind initial (sumWords acc)))) := by
    apply storeBytes_success
    simpa [bytes32] using writable
  cases kind with
  | signed =>
    simp only [outputScalar] at store
    have defn := defined
    change -2147483648 ≤ initial.toInt + (sumWords acc).toInt ∧ initial.toInt + (sumWords acc).toInt < 2147483648 at defn
    apply run_sound (fuel := 10)
    simp +contextual [rvvFinish, rvvProgram, Generated.QS8Rsum.rvv, dropStatements,
      run, eval, intrinsic, reductionIntrinsic, effect, binary, update, rvvFinished,
      loc.vacc, loc.outputPtr, loc.vlmax, ha, cap, positive, seedPos, seedNonneg, seedIntPos, seedNat, headZero, oldHeadZero, headSingle, takeAcc,
      load, defn, value, outputScalar, store]
  | unsigned =>
    simp only [outputScalar] at store
    have defn := outputScalar_unsigned_bounds initial (sumWords acc)
    simp [outputScalar] at defn
    simp at store
    have repr : max (initial.toInt % 4294967296) 0 = (initial.toNat : Int) := by
      have h := congrArg (fun x : BitVec 32 => (x.toNat : Int)) (BitVec.ofInt_toInt (x := initial))
      simpa only [BitVec.toNat_ofInt, Int.ofNat_toNat, Nat.reducePow, Int.reduceNatCast] using h
    apply run_sound (fuel := 10)
    simp +contextual [rvvFinish, rvvProgram, Generated.QU8Rsum.rvv, dropStatements,
      run, eval, intrinsic, reductionIntrinsic, effect, binary, update, rvvFinished,
      loc.vacc, loc.outputPtr, loc.vlmax, ha, cap, positive, seedPos, seedNonneg, seedIntPos, seedNat, headZero, oldHeadZero, headSingle, takeAcc,
      load, defn, value, outputScalar, convert, store, repr]

theorem sumWords_zeros (n : Nat) : sumWords (List.replicate n (0#32)) = 0#32 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, sumWords_cons, ih]; simp

/-- Complete RVV execution, including assertions, accumulator initialization,
unbounded loop, reduction and final checked/wrapping scalar memory update.
This is one side of the intended pair theorem; it does not establish NEON/RVV
equivalence without the independent source proof. -/
theorem rvv_correct (cfg : Config) (kind : Interpretation) (s : State) (c : Call)
    (h : Entry kind s c) (capacity : 8 ≤ cfg.capacity) :
    ∃ t, Exec cfg (rvvProgram kind) s t ∧ t.memory = resultMemory kind s.memory c := by
  let start := rvvInitialized s cfg.capacity
  have init : Exec cfg (takeStatements 6 (rvvProgram kind)) s start := rvv_init_exec cfg kind s c h
  have loc := rvvInitialized_locals cfg kind s c h
  have read : ∀ a, Footprint c.input c.count a → start.memory.readable a = true :=
    fun a ha => h.readable a (footprint_mono (by omega) ha)
  obtain ⟨t, acc, loop, memory, locals, length, sum⟩ := rvv_loop_total cfg kind start c.count c.input c.output
    (List.replicate cfg.capacity 0) loc h.size (by simp) read
  have mem : t.memory = s.memory := memory
  have total : sumWords acc = byteSum kind s.memory c.input c.count := by
    simpa [sumWords_zeros, byteSum, start, rvvInitialized, update] using sum
  have load : loadParam t.memory c.output = some (.integer c.initial.toInt) := by
    rw [mem]; exact h.initialLoad
  have defined : OutputDefined kind c.initial (sumWords acc) := by rw [total]; exact h.defined
  have writable : ∀ a, Footprint c.output 4 a → t.memory.writable a = true := by
    rw [mem]; exact h.writable
  have finish := rvv_finish_exec cfg kind t (c.input + BitVec.ofNat 64 c.count) c.output acc c.initial
    locals length capacity load defined writable
  rw [mem, total] at finish
  let final := rvvFinished kind t acc (resultMemory kind s.memory c)
  have finished : Exec cfg (rvvFinish kind) t final := finish
  refine ⟨final, ?_, rfl⟩
  have rest : Exec cfg (.seq (rvvLoop kind) (rvvFinish kind)) start final := .seq loop finished
  have shape : dropStatements 6 (rvvProgram kind) = .seq (rvvLoop kind) (rvvFinish kind) := by
    cases kind <;> rfl
  rw [← shape] at rest
  exact exec_take_drop 6 init rest

end Salty.Kernels.Rsum
