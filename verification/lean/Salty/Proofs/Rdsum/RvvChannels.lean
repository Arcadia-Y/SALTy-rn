import Salty.Proofs.Rdsum.ChannelMemory

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 2000000

def rvvChannelLoop (kind : Interpretation) : Stmt := firstStatement (dropStatements 5 (rvvProgram kind))

theorem rvv_channel_loop_shape (kind : Interpretation) : rvvChannelLoop kind =
    .loop (.bin .gt (.var "channels") (.cast .u64 (.lit 0))) (rvvChannels kind) := by cases kind <;> rfl

/-- The complete scalable channel loop terminates for every positive bounded
VL schedule and produces the original-memory scalar row-sum specification. -/
theorem rvv_channels_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero output : Address) (rows stride channels : Nat)
    (rowBound : rows < 2^31) (channelBound : channels < 2^64)
    (loc : ChannelLocals s rows channels stride input zero output)
    (safe : ChannelSafe s.memory input zero output rows stride channels) :
    ∃ t, Exec cfg (rvvChannelLoop kind) s t ∧
      t.memory = writeBytes s.memory output (encodeWords32 (stripWords kind s.memory input output rows stride channels)) := by
  induction channels using Nat.strongRecOn generalizing s input output with
  | ind channels ih =>
    by_cases empty : channels = 0
    · subst channels
      refine ⟨s,?_,?_⟩
      · rw [rvv_channel_loop_shape]
        apply Exec.done (v := .integer 0)
        · simp [eval, binary, loc.channels, show convert .u64 0 = 0 by decide]
        · rfl
      · rfl
    · let width := cfg.choose channels
      have positive : 0 < width := cfg.positive channels (by omega)
      have within : width ≤ channels := Nat.le_trans (cfg.bounded channels) (Nat.min_le_left ..)
      obtain ⟨u,body,mem,uloc⟩ := rvv_channel_correct kind cfg s input zero output rows stride channels rowBound channelBound loc
        (fun row hr a ha => safe.inputRead row hr a (footprint_mono within ha))
        (fun a ha => safe.zeroRead a (footprint_mono within ha))
        (fun column hc => safe.zeros _ ⟨column,by omega,rfl⟩)
        (fun a ha => safe.outRead a (footprint_mono (by omega) ha))
        (fun a ha => safe.outWrite a (footprint_mono (by omega) ha))
      have nextSafe : ChannelSafe u.memory (input+BitVec.ofNat 64 width) zero
          (output+BitVec.ofNat 64 (4*width)) rows stride (channels-width) := by
        rw [mem]
        exact safe.advance within _ (by simp [width])
      obtain ⟨t,rest,tmem⟩ := ih (channels-width) (by omega) u (input+BitVec.ofNat 64 width)
        (output+BitVec.ofNat 64 (4*width)) (by omega) uloc nextSafe
      refine ⟨t,?_,?_⟩
      · rw [rvv_channel_loop_shape]
        apply Exec.more (v := .integer 1) (t := u)
        · simp [eval, binary, loc.channels, empty, show (0 : Int) < channels by omega,
            show convert .u64 0 = 0 by decide]
        · rfl
        · exact body
        · simpa only [← rvv_channel_loop_shape] using rest
      · rw [tmem, mem]
        exact strip_write_join kind s.memory input zero output rows stride channels width safe within

end Salty.Kernels.Rdsum
