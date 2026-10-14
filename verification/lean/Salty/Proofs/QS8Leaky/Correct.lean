import Salty.Spec.QS8Leaky
import Salty.Proofs.QS8Leaky.Neon
import Salty.Proofs.Core.CByteMachine

namespace Salty.Kernels.QS8Leaky
open CByte
open S8Clamp.Execution (PaddedSafe)

def neonInit : Stmt := takeStatements 8 Generated.QS8Leaky.neon
def rvvInit : Stmt := takeStatements 8 Generated.QS8Leaky.rvv

def neonInitialized (s : State) (c : Call) : State :=
  let t := update s "vinput_zero_point" (.halfwords (List.replicate 8 c.values.inputZero))
  let t := update t "vpositive_multiplier" (.halfwords (List.replicate 8 c.values.positive))
  let t := update t "vnegative_multiplier" (.halfwords (List.replicate 8 c.values.negative))
  update t "voutput_zero_point" (.halfwords (List.replicate 8 c.values.outputZero))

def rvvInitialized (s : State) (c : Call) : State :=
  let t := update s "input_zero_point" (.integer c.values.inputZero.toInt)
  let t := update t "positive_multiplier" (.integer c.values.positive.toInt)
  let t := update t "negative_multiplier" (.integer c.values.negative.toInt)
  update t "output_zero_point" (.integer c.values.outputZero.toInt)

theorem negation_range (m : BitVec 32) (defined : m.toInt ≠ -(2^31)) :
    -(2^31) < m.toInt ∧ m.toInt < 2^31 := by
  have lo := BitVec.le_toInt m
  have hi := BitVec.toInt_lt (x := m)
  constructor <;> omega

set_option maxHeartbeats 1000000 in
theorem neon_init_exec (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    Exec cfg neonInit s (neonInitialized s c) := by
  have hn : c.count ≠ 0 := by have := h.positive; omega
  have hi : c.input ≠ 0#64 := h.inputNonzero
  have ho : c.output ≠ 0#64 := h.outputNonzero
  have hp : -2147483648 < c.positive.toInt ∧ c.positive.toInt < 2147483648 :=
    negation_range c.positive h.positiveDefined
  have hm : -2147483648 < c.negative.toInt ∧ c.negative.toInt < 2147483648 :=
    negation_range c.negative h.negativeDefined
  have twice (n : Int) : BitVec.ofInt 16 (n.bmod 65536) = BitVec.ofInt 16 n := by
    simpa [BitVec.toInt_ofInt] using (BitVec.ofInt_toInt (x := BitVec.ofInt 16 n))
  apply run_sound (fuel := 20)
  simp +contextual (maxSteps := 1000000) [neonInit, takeStatements, Generated.QS8Leaky.neon,
    run, eval, truth, effect, intrinsic, saturatingIntrinsic, binary, convert,
    h.batch, h.inputPtr, h.outputPtr, h.paramsPtr, h.inputZeroLoad, h.positiveLoad, h.negativeLoad,
    h.outputZeroLoad, hi, ho, hn, hp, hm, Int.max_def, update, neonInitialized, Call.values, twice]

set_option maxHeartbeats 1000000 in
theorem rvv_init_exec (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    Exec cfg rvvInit s (rvvInitialized s c) := by
  have hn : c.count ≠ 0 := by have := h.positive; omega
  have hi : c.input ≠ 0#64 := h.inputNonzero
  have ho : c.output ≠ 0#64 := h.outputNonzero
  have hp : -2147483648 < c.positive.toInt ∧ c.positive.toInt < 2147483648 :=
    negation_range c.positive h.positiveDefined
  have hm : -2147483648 < c.negative.toInt ∧ c.negative.toInt < 2147483648 :=
    negation_range c.negative h.negativeDefined
  apply run_sound (fuel := 20)
  simp +contextual (maxSteps := 1000000) [rvvInit, takeStatements, Generated.QS8Leaky.rvv,
    run, eval, truth, effect, binary, convert, h.batch, h.inputPtr, h.outputPtr,
    h.paramsPtr, h.inputZeroLoad, h.positiveLoad, h.negativeLoad, h.outputZeroLoad,
    hi, ho, hn, hp, hm, Int.max_def, update, rvvInitialized, Call.values]

theorem neon_initialized_locals (s : State) (c : Call) (h : Entry s c) :
    NeonLocals (neonInitialized s c) c.count c.input c.output c.values := by
  constructor <;> simp [neonInitialized, update, h.batch, h.inputPtr, h.outputPtr]

theorem rvv_initialized_locals (s : State) (c : Call) (h : Entry s c) :
    RvvLocals (rvvInitialized s c) c.count c.input c.output c.values := by
  constructor <;> simp [rvvInitialized, update, h.batch, h.inputPtr, h.outputPtr]

theorem neon_correct (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    ∃ t, Exec cfg Generated.QS8Leaky.neon s t ∧ t.memory = resultMemory s c := by
  obtain ⟨t, hrun, hm⟩ := neon8_tail_total cfg (neonInitialized s c) c.count c.input c.output
    c.values (neon_initialized_locals s c h) h.size h.memory
  exact ⟨t, exec_take_drop 8 (neon_init_exec cfg s c h) hrun, hm⟩

theorem rvv_correct (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    ∃ t, Exec cfg Generated.QS8Leaky.rvv s t ∧ t.memory = resultMemory s c := by
  obtain ⟨t, hrun, hm⟩ := rvv_loop_total cfg (rvvInitialized s c) c.count c.input c.output
    c.values (rvv_initialized_locals s c h) h.size h.memory.region
  refine ⟨t, exec_take_drop 8 (rvv_init_exec cfg s c h) (.seq hrun .skip), ?_⟩
  have lane : rvvLane c.values = neonLane c.values := (funext (QuantizedLeakyISA.leaky_lane_eq c.values)).symm
  simpa only [lane] using hm

/-- Both complete programs execute independently to the common full-memory
result. No output equality is assumed by Entry. -/
theorem extracted_equivalent (cfg : Config) (c : Call) :
    CByte.Equivalent cfg Generated.QS8Leaky.neon Generated.QS8Leaky.rvv (fun s => Entry s c) := by
  intro s h
  obtain ⟨a, ha, hma⟩ := neon_correct cfg s c h
  obtain ⟨b, hb, hmb⟩ := rvv_correct cfg s c h
  exact ⟨a, b, ha, hb, hma.trans hmb.symm⟩

/-- Shared return/fault/divergence relation for the defined ABI-call domain.
Quantification over cfg covers every progressing bounded RVV VL choice. -/
theorem behavior_equivalent_proof (cfg : Config) (c : Call) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.QS8Leaky.neon], s⟩)
      (fun s => ⟨[Generated.QS8Leaky.rvv], s⟩) (fun s => Entry s c) :=
  (extracted_equivalent cfg c).behavior

theorem result_frame (s : State) (c : Call) (a : Address)
    (outside : ¬ Footprint c.output c.count a) : (resultMemory s c).data a = s.memory.data a := by
  apply writeBytes_frame
  simpa only [List.length_map, readBytes_length] using outside

end Salty.Kernels.QS8Leaky
