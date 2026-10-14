import Salty.Proofs.Rdsum.NeonChannels

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

theorem neon_entry_shape (kind : Interpretation) : takeStatements 5 (neonProgram kind) = rvvEntry kind := by
  cases kind <;> rfl

/-- Complete extracted NEON function correctness, with unbounded row/channel
loops and the original scalar specification of all output words. -/
theorem neon_correct (kind : Interpretation) (cfg : Config) (s : State) (c : Call)
    (entry : Entry kind s c) :
    ∃ t, Exec cfg (neonProgram kind) s t ∧ t.memory = resultMemory kind s.memory c := by
  let u := update s "input_increment" (.integer (7*c.stride))
  have initial : Exec cfg (takeStatements 5 (neonProgram kind)) s u := by
    rw [neon_entry_shape]
    exact rvv_entry_exec kind cfg s c entry
  have loc : ChannelLocals u c.rows c.channels c.stride c.input c.zero c.output := by
    constructor <;> simp [u, update, entry.rowsLocal, entry.channelsLocal, entry.strideLocal,
      entry.inputLocal, entry.zeroLocal, entry.outputLocal]
  obtain ⟨t,loops,mem,_⟩ := neon_channels_correct kind cfg u c.input c.zero c.output c.rows c.stride c.channels
    entry.rowsInt entry.strideSize entry.channelsSize loc entry.neon_safe
  exact ⟨t,exec_take_drop 5 initial loops,mem⟩

end Salty.Kernels.Rdsum
