import Salty.Spec.QU8Add
import Salty.Proofs.QU8Add.Neon
import Salty.Proofs.QU8Add.Rvv
import Salty.Proofs.Core.CByteMachine
import Salty.Proofs.QS8Add.InitShift

namespace Salty.Kernels.QU8Add
open CByte QuantizedUAddISA
open SIMD.Unsigned
open QS8Add (rvv_shift_byte_eval rvv_shift_count_eval)

def neonInit : Stmt := takeStatements 13 Generated.QU8Add.neon
def rvvInit : Stmt := takeStatements 14 Generated.QU8Add.rvv

def neonInitialized (s : State) (c : Call) : State :=
  let p := c.values
  let t := update s "va_zero_point" (.vector 1 (List.replicate 8 p.aZero))
  let t := update t "vb_zero_point" (.vector 1 (List.replicate 8 p.bZero))
  let t := update t "va_multiplier" (.words32 (List.replicate 4 p.aMultiplier))
  let t := update t "vb_multiplier" (.words32 (List.replicate 4 p.bMultiplier))
  let t := update t "vright_shift" (.words32 (List.replicate 4 (-p.shift)))
  let t := update t "voutput_zero_point" (.halfwords (List.replicate 8 p.outputZero))
  let t := update t "voutput_min" (.vector 1 (List.replicate 8 p.outputMin))
  update t "voutput_max" (.vector 1 (List.replicate 8 p.outputMax))

def rvvBaseInitialized (s : State) (c : Call) : State :=
  let p := c.values
  let t := update s "a_zero_point" (.integer p.aZero.toNat)
  let t := update t "b_zero_point" (.integer p.bZero.toNat)
  let t := update t "a_multiplier" (.integer p.aMultiplier.toInt)
  update t "b_multiplier" (.integer p.bMultiplier.toInt)

def rvvShiftInitialized (s : State) (p : Params) : State :=
  update (update s "shift_byte" (.integer (((-p.shift).toNat % 256 : Nat) : Int)))
    "shift" (.integer (ShiftISA.rvvCount p.shift))

def rvvOutputInitialized (s : State) (p : Params) : State :=
  let t := update s "output_zero_point" (.integer p.outputZero.toInt)
  let t := update t "output_min" (.integer p.outputMin.toNat)
  update t "output_max" (.integer p.outputMax.toNat)

def rvvInitialized (s : State) (c : Call) : State :=
  rvvOutputInitialized (rvvShiftInitialized (rvvBaseInitialized s c) c.values) c.values

set_option maxHeartbeats 1000000 in
theorem neon_init_exec (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    Exec cfg neonInit s (neonInitialized s c) := by
  have hn : c.count ≠ 0 := by have := h.positive; omega
  have ha : c.inputA ≠ 0#64 := h.inputANonzero
  have hb : c.inputB ≠ 0#64 := h.inputBNonzero
  have ho : c.output ≠ 0#64 := h.outputNonzero
  have defined : -2147483648 < c.values.shift.toInt ∧ c.values.shift.toInt < 2147483648 := by
    have := BitVec.le_toInt c.values.shift
    have := BitVec.toInt_lt (x := c.values.shift)
    have := h.shiftDefined
    constructor <;> omega
  apply run_sound (fuel := 28)
  simp +contextual (maxSteps := 1000000) [neonInit, takeStatements, Generated.QU8Add.neon,
    run, eval, truth, effect, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic, unsignedArithmeticIntrinsic,
    binary, convert, h.batch, h.inputAPtr, h.inputBPtr, h.outputPtr, h.paramsPtr,
    h.zeroALoad, h.zeroBLoad, h.multALoad, h.multBLoad, h.shiftLoad, h.outputZeroLoad,
    h.outputMinLoad, h.outputMaxLoad, ha, hb, ho, hn, defined, Int.max_def, update,
    neonInitialized, BitVec.ofInt_neg]

set_option maxHeartbeats 1000000 in
theorem rvv_base_init_exec (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    Exec cfg (takeStatements 9 Generated.QU8Add.rvv) s (rvvBaseInitialized s c) := by
  have hn : c.count ≠ 0 := by have := h.positive; omega
  have ha : c.inputA ≠ 0#64 := h.inputANonzero
  have hb : c.inputB ≠ 0#64 := h.inputBNonzero
  have ho : c.output ≠ 0#64 := h.outputNonzero
  apply run_sound (fuel := 20)
  simp +contextual [takeStatements, Generated.QU8Add.rvv, run, eval, truth, effect,
    binary, convert, h.batch, h.inputAPtr, h.inputBPtr, h.outputPtr, h.paramsPtr,
    h.zeroALoad, h.zeroBLoad, h.multALoad, h.multBLoad,
    ha, hb, ho, hn, Int.max_def, update, rvvBaseInitialized]

theorem rvv_shift_init_exec (cfg : Config) (s : State) (param : Address) (p : Params)
    (ptr : s.locals "params" = some (.pointer param))
    (load : loadParam s.memory (param+16#64) = some (.integer p.shift.toInt)) :
    Exec cfg (takeStatements 2 (dropStatements 9 Generated.QU8Add.rvv)) s (rvvShiftInitialized s p) := by
  apply Exec.seq (.assign (rvv_shift_byte_eval cfg s param p.shift ptr load))
  apply Exec.seq _ .skip
  apply Exec.assign
  exact rvv_shift_count_eval cfg _ p.shift (by simp [update])

theorem rvv_output_init_exec (cfg : Config) (s : State) (param : Address) (p : Params)
    (ptr : s.locals "params" = some (.pointer param))
    (zero : loadParam16 s.memory (param+20#64) = some (.integer p.outputZero.toInt))
    (lo : s.memory.load (param+22#64) = some p.outputMin)
    (hi : s.memory.load (param+23#64) = some p.outputMax) :
    Exec cfg (takeStatements 3 (dropStatements 11 Generated.QU8Add.rvv)) s (rvvOutputInitialized s p) := by
  apply run_sound (fuel := 8)
  simp [takeStatements, dropStatements, Generated.QU8Add.rvv, run, eval, update,
    ptr, zero, lo, hi, rvvOutputInitialized]

theorem rvv_init_exec (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    Exec cfg rvvInit s (rvvInitialized s c) := by
  let base := rvvBaseInitialized s c
  let shifted := rvvShiftInitialized base c.values
  have hb := rvv_base_init_exec cfg s c h
  have hs := rvv_shift_init_exec cfg base c.params c.values
    (by simp [base, rvvBaseInitialized, update, h.paramsPtr]) h.shiftLoad
  have ho := rvv_output_init_exec cfg shifted c.params c.values
    (by simp [shifted, base, rvvShiftInitialized, rvvBaseInitialized, update, h.paramsPtr])
    h.outputZeroLoad h.outputMinLoad h.outputMaxLoad
  exact exec_take_drop 9 hb (exec_take_drop 2 hs ho)

theorem neon_initialized_locals (s : State) (c : Call) (h : Entry s c) :
    NeonLocals (neonInitialized s c) c.count c.inputA c.inputB c.output c.values := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> simp [neonInitialized, update]
  all_goals simp [neonInitialized, update, h.batch, h.inputAPtr, h.inputBPtr, h.outputPtr]

theorem rvv_initialized_locals (s : State) (c : Call) (h : Entry s c) :
    RvvLocals (rvvInitialized s c) c.count c.inputA c.inputB c.output c.values := by
  constructor <;> simp [rvvInitialized, rvvOutputInitialized, rvvShiftInitialized, rvvBaseInitialized,
    update, h.batch, h.inputAPtr, h.inputBPtr, h.outputPtr]

theorem neon_correct (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    ∃ t, Exec cfg Generated.QU8Add.neon s t ∧ t.memory = resultMemory s c := by
  obtain ⟨t, hr, hm⟩ := neon_main_tail_total cfg (neonInitialized s c) c.count c.inputA c.inputB c.output
    c.values (neon_initialized_locals s c h) h.size h.memory
  exact ⟨t, exec_take_drop 13 (neon_init_exec cfg s c h) hr, hm⟩

theorem rvv_correct (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    ∃ t, Exec cfg Generated.QU8Add.rvv s t ∧ t.memory = resultMemory s c := by
  obtain ⟨t, hr, hm⟩ := rvv_loop_total cfg (rvvInitialized s c) c.count c.inputA c.inputB c.output
    c.values (rvv_initialized_locals s c h) h.size (h.memory.weaken_padding (by omega))
  refine ⟨t, exec_take_drop 14 (rvv_init_exec cfg s c h) (.seq hr .skip), ?_⟩
  have lane : rvvLane c.values = neonLane c.values :=
    funext (fun a => funext (fun b => (addition_lane_eq c.values a b).symm))
  simpa only [lane] using hm

/-- Independently executed whole functions reach the same full-memory result;
Entry assumes parameter loads and caller safety, never output equality. -/
theorem extracted_equivalent (cfg : Config) (c : Call) :
    CByte.Equivalent cfg Generated.QU8Add.neon Generated.QU8Add.rvv (fun s => Entry s c) := by
  intro s h
  obtain ⟨a, ha, hma⟩ := neon_correct cfg s c h
  obtain ⟨b, hb, hmb⟩ := rvv_correct cfg s c h
  exact ⟨a, b, ha, hb, hma.trans hmb.symm⟩

/-- Common return/fault/divergence relation for every defined call and every
bounded progressing RVV vector-length choice. Arithmetic flags are unobserved. -/
theorem behavior_equivalent_proof (cfg : Config) (c : Call) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QU8Add.neon], s⟩)
      (fun s => ⟨[Generated.QU8Add.rvv], s⟩) (fun s => Entry s c) :=
  (extracted_equivalent cfg c).behavior

theorem result_frame (s : State) (c : Call) (a : Address)
    (outside : ¬ Footprint c.output c.count a) : (resultMemory s c).data a = s.memory.data a :=
  binaryResult_frame _ _ _ _ _ _ _ outside

end Salty.Kernels.QU8Add
