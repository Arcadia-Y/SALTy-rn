import Salty.Proofs.Rdsum.RvvChannels

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def rvvEntry (kind : Interpretation) : Stmt := takeStatements 5 (rvvProgram kind)

theorem rvv_entry_exec (kind : Interpretation) (cfg : Config) (s : State) (c : Call)
    (entry : Entry kind s c) :
    Exec cfg (rvvEntry kind) s (update s "input_increment" (.integer (7*c.stride))) := by
  have product : convert .u64 (7*(c.stride : Int)) = (7*c.stride : Nat) := by
    have h := cast_nat (7*c.stride) entry.strideSize
    simpa only [Int.natCast_mul] using h
  have inputNZ : c.input ≠ 0#64 := entry.inputNonzero
  have outputNZ : c.output ≠ 0#64 := entry.outputNonzero
  have rp : c.rows ≠ 0 := by have := entry.rowsPositive; omega
  have cp : c.channels ≠ 0 := by have := entry.channelsPositive; omega
  cases kind <;> apply run_sound (fuel := 8) <;>
    simp [rvvEntry, rvvProgram, Generated.QS8Rdsum.rvv, Generated.QU8Rdsum.rvv,
      takeStatements, run, eval, binary, truth, effect, entry.rowsLocal, entry.channelsLocal,
      entry.inputLocal, entry.outputLocal, entry.strideLocal, inputNZ, outputNZ,
      rp, cp, product, show convert .u64 0 = 0 by decide, show convert .u64 7 = 7 by decide]

/-- Complete RVV function correctness for either signed or unsigned byte rows.
The result is the scalar original-memory sum plus the old output word, modulo
2^32, with all other bytes and permissions preserved. -/
theorem rvv_correct (kind : Interpretation) (cfg : Config) (s : State) (c : Call)
    (entry : Entry kind s c) :
    ∃ t, Exec cfg (rvvProgram kind) s t ∧ t.memory = resultMemory kind s.memory c := by
  let u := update s "input_increment" (.integer (7*c.stride))
  have initial : Exec cfg (rvvEntry kind) s u := rvv_entry_exec kind cfg s c entry
  have loc : ChannelLocals u c.rows c.channels c.stride c.input c.zero c.output := by
    constructor <;> simp [u, update, entry.rowsLocal, entry.channelsLocal, entry.strideLocal,
      entry.inputLocal, entry.zeroLocal, entry.outputLocal]
  obtain ⟨t,loop,mem⟩ := rvv_channels_correct kind cfg u c.input c.zero c.output c.rows c.stride c.channels
    entry.rowsInt entry.channelsSize loc entry.channel_safe
  refine ⟨t,?_,mem⟩
  apply exec_take_drop (t := u) 5 initial
  have shape : dropStatements 5 (rvvProgram kind) = .seq (rvvChannelLoop kind) .skip := by cases kind <;> rfl
  rw [shape]
  exact .seq loop .skip

end Salty.Kernels.Rdsum
