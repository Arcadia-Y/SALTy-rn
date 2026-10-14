import Salty.Spec.S8Clamp
import Salty.Proofs.S8Clamp.Neon
import Salty.Proofs.Core.CByteMachine

namespace Salty.Kernels.S8Clamp.Execution
open CByte

def neonInit : Stmt := takeStatements 6 Generated.S8Clamp.neon
def rvvInit : Stmt := takeStatements 6 Generated.S8Clamp.rvv

def neonInitialized (s : State) (c : Call) : State :=
  let t := update s "voutput_max" (.vector 1 (List.replicate 16 c.bounds.hi))
  update t "voutput_min" (.vector 1 (List.replicate 16 c.bounds.lo))

def rvvInitialized (s : State) (c : Call) : State :=
  let t := update s "min" (.integer c.bounds.lo.toInt)
  update t "max" (.integer c.bounds.hi.toInt)

theorem narrow_twice (x : Int) : BitVec.ofInt 8 (x.bmod 256) = BitVec.ofInt 8 x := by
  simpa [BitVec.toInt_ofInt] using (BitVec.ofInt_toInt (x := BitVec.ofInt 8 x))

theorem neon_init_exec (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    Exec cfg neonInit s (neonInitialized s c) := by
  have hn : c.count ≠ 0 := by have := h.positive; omega
  have hi : c.input ≠ 0#64 := h.inputNonzero
  have ho : c.output ≠ 0#64 := h.outputNonzero
  apply run_sound (fuel := 20)
  simp [neonInit, takeStatements, Generated.S8Clamp.neon, run, eval, truth, effect,
    intrinsic, binary, convert, h.batch, h.inputPtr, h.outputPtr, h.paramsPtr,
    h.minLoad, h.maxLoad, hi, ho, hn, Int.max_def,
    update, neonInitialized, Call.bounds, narrow_twice]

theorem rvv_init_exec (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    Exec cfg rvvInit s (rvvInitialized s c) := by
  have hn : c.count ≠ 0 := by have := h.positive; omega
  have hi : c.input ≠ 0#64 := h.inputNonzero
  have ho : c.output ≠ 0#64 := h.outputNonzero
  apply run_sound (fuel := 20)
  simp [rvvInit, takeStatements, Generated.S8Clamp.rvv, run, eval, truth, effect,
    binary, convert, h.batch, h.inputPtr, h.outputPtr, h.paramsPtr,
    h.minLoad, h.maxLoad, hi, ho, hn, Int.max_def,
    update, rvvInitialized, Call.bounds]

theorem neon_initialized_locals (s : State) (c : Call) (h : Entry s c) :
    NeonLocals (neonInitialized s c) c.count c.input c.output c.bounds := by
  constructor <;> simp [neonInitialized, update, h.batch, h.inputPtr, h.outputPtr]

theorem rvv_initialized_locals (s : State) (c : Call) (h : Entry s c) :
    RvvLocals (rvvInitialized s c) c.count c.input c.output c.bounds := by
  constructor <;> simp [rvvInitialized, update, h.batch, h.inputPtr, h.outputPtr]

theorem neon_correct (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    ∃ t, Exec cfg Generated.S8Clamp.neon s t ∧ t.memory = resultMemory s c := by
  obtain ⟨t, hrun, hm⟩ := neon_suffix_total cfg (neonInitialized s c) c.count c.input c.output
    c.bounds h.ordered (neon_initialized_locals s c h) h.size h.memory
  exact ⟨t, exec_take_drop 6 (neon_init_exec cfg s c h) hrun, hm⟩

theorem rvv_correct (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    ∃ t, Exec cfg Generated.S8Clamp.rvv s t ∧ t.memory = resultMemory s c := by
  obtain ⟨t, hrun, hm⟩ := rvv_loop_total cfg (rvvInitialized s c) c.count c.input c.output
    c.bounds (rvv_initialized_locals s c h) h.size h.memory.region
  exact ⟨t, exec_take_drop 6 (rvv_init_exec cfg s c h) (.seq hrun .skip), hm⟩

/-- Whole-program equivalence of the independently extracted intrinsic models.
The AST/ABI/intrinsic frontend bridge is trusted, and compiler/binary correctness
is not claimed. Defined executions terminate and agree on the entire memory. -/
theorem extracted_equivalent (cfg : Config) (c : Call) :
    CByte.Equivalent cfg Generated.S8Clamp.neon Generated.S8Clamp.rvv (fun s => Entry s c) := by
  intro s h
  obtain ⟨a, ha, hma⟩ := neon_correct cfg s c h
  obtain ⟨b, hb, hmb⟩ := rvv_correct cfg s c h
  exact ⟨a, b, ha, hb, hma.trans hmb.symm⟩

/-- The suite theorem uses the common outcome relation. Every legal RVV
schedule is covered by quantification over cfg; no maximum-VL assumption is made.
Full memory, return, faults, and divergence are compared on the defined domain. -/
theorem behavior_equivalent_proof (cfg : Config) (c : Call) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.S8Clamp.neon], s⟩)
      (fun s => ⟨[Generated.S8Clamp.rvv], s⟩) (fun s => Entry s c) :=
  (extracted_equivalent cfg c).behavior

theorem result_frame (s : State) (c : Call) (a : Address)
    (outside : ¬ Footprint c.output c.count a) : (resultMemory s c).data a = s.memory.data a := by
  apply writeBytes_frame
  simpa only [List.length_map, readBytes_length] using outside

end Salty.Kernels.S8Clamp.Execution
