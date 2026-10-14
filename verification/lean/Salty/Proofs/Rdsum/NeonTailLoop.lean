import Salty.Proofs.Rdsum.NeonSafety

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def neonTailDo (kind : Interpretation) : Stmt :=
  firstStatement (dropStatements (match kind with | .signed => 1 | .unsigned => 2)
    (branchYes (firstStatement (dropStatements 6 (neonProgram kind)))))

def neonTailLoop (kind : Interpretation) : Stmt := dropStatements 1 (neonTailDo kind)

theorem neon_tail_loop_shape (kind : Interpretation) : neonTailLoop kind =
    .loop (.bin .ne (.var "channels") (.cast .u64 (.lit 0))) (neonChannels kind false) := by
  cases kind <;> rfl

theorem neon_tail_do_shape (kind : Interpretation) : neonTailDo kind =
    .seq (neonChannels kind false) (neonTailLoop kind) := by cases kind <;> rfl

theorem neon_tail_channel_safe (kind : Interpretation) (cfg : Config) (s : State)
    (input zero output : Address) (rows stride channels : Nat)
    (rowBound : rows < 2^31) (channelBound : channels < 2^64)
    (loc : ChannelLocals s rows channels stride input zero output)
    (safe : NeonSafe kind s.memory input zero output rows stride channels) :
    ∃ t, Exec cfg (neonChannels kind false) s t ∧
      t.memory = writeBytes s.memory output (encodeWords32 (stripWords kind s.memory input output rows stride (min channels 8))) ∧
      (if 8 ≤ channels then ChannelLocals t rows (channels-8) stride (input+8) zero (output+32)
       else t.locals "channels" = some (.integer 0)) := by
  exact neon_tail_channel_correct kind cfg s input zero output rows stride channels rowBound channelBound loc
    (fun row hr a ha => safe.inputPadRead row hr a (footprint_mono (by omega) ha))
    (fun a ha => safe.zeroPadRead a (footprint_mono (by decide) ha))
    (fun col hc => safe.zeroPadContents _ ⟨col,by omega,rfl⟩)
    (fun a ha => safe.outRead a (footprint_mono (by have := Nat.min_le_left channels 8; omega) ha))
    (fun a ha => safe.outWrite a (footprint_mono (by have := Nat.min_le_left channels 8; omega) ha))
    (fun h => safe.scalarDefined.tail h)

/-- Complete eight-channel tail loop, including a final 4/2/1 suffix. -/
theorem neon_tail_loop_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero output : Address) (rows stride channels : Nat)
    (rowBound : rows < 2^31) (channelBound : channels < 2^64)
    (loc : ChannelLocals s rows channels stride input zero output)
    (safe : NeonSafe kind s.memory input zero output rows stride channels) :
    ∃ t, Exec cfg (neonTailLoop kind) s t ∧
      t.memory = writeBytes s.memory output (encodeWords32 (stripWords kind s.memory input output rows stride channels)) ∧
      t.locals "channels" = some (.integer 0) := by
  induction channels using Nat.strongRecOn generalizing s input output with
  | ind channels ih =>
    by_cases empty : channels = 0
    · subst channels
      refine ⟨s,?_,rfl,loc.channels⟩
      rw [neon_tail_loop_shape]
      apply Exec.done (v := .integer 0)
      · simp [eval, binary, loc.channels, show convert .u64 0 = 0 from rfl]
      · rfl
    · obtain ⟨u,body,mem,uloc⟩ := neon_tail_channel_safe kind cfg s input zero output rows stride channels rowBound channelBound loc safe
      by_cases large : 8 ≤ channels
      · have nextLoc : ChannelLocals u rows (channels-8) stride (input+8) zero (output+32) := by simpa only [if_pos large] using uloc
        rw [Nat.min_eq_right large] at mem
        have nextSafe : NeonSafe kind u.memory (input+8) zero (output+32) rows stride (channels-8) := by
          rw [mem]
          exact safe.advance large (by decide) _ (by simp)
        obtain ⟨t,rest,tmem,tchannels⟩ := ih (channels-8) (by omega) u (input+8) (output+32) (by omega) nextLoc nextSafe
        refine ⟨t,?_,?_,tchannels⟩
        · rw [neon_tail_loop_shape]
          apply Exec.more (v := .integer 1) (t := u)
          · simp [eval, binary, loc.channels, empty, show convert .u64 0 = 0 from rfl]
          · rfl
          · exact body
          · simpa only [← neon_tail_loop_shape] using rest
        · rw [tmem, mem]
          exact strip_write_join kind s.memory input zero output rows stride channels 8 safe.toChannelSafe large
      · have finished : u.locals "channels" = some (.integer 0) := by simpa only [if_neg large] using uloc
        refine ⟨u,?_,?_,finished⟩
        · rw [neon_tail_loop_shape]
          apply Exec.more (v := .integer 1) (t := u)
          · simp [eval, binary, loc.channels, empty, show convert .u64 0 = 0 from rfl]
          · rfl
          · exact body
          · apply Exec.done (v := .integer 0)
            · simp [eval, binary, finished, show convert .u64 0 = 0 from rfl]
            · rfl
        · simpa only [Nat.min_eq_left (by omega : channels ≤ 8)] using mem

/-- The source tail is a do/while: its first iteration is mandatory and starts
only under the surrounding nonzero-channel guard. -/
theorem neon_tail_do_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero output : Address) (rows stride channels : Nat)
    (positive : 0 < channels) (rowBound : rows < 2^31) (channelBound : channels < 2^64)
    (loc : ChannelLocals s rows channels stride input zero output)
    (safe : NeonSafe kind s.memory input zero output rows stride channels) :
    ∃ t, Exec cfg (neonTailDo kind) s t ∧
      t.memory = writeBytes s.memory output (encodeWords32 (stripWords kind s.memory input output rows stride channels)) ∧
      t.locals "channels" = some (.integer 0) := by
  obtain ⟨t,loop,mem,done⟩ := neon_tail_loop_correct kind cfg s input zero output rows stride channels rowBound channelBound loc safe
  refine ⟨t,?_,mem,done⟩
  rw [neon_tail_loop_shape] at loop
  cases loop with
  | done he ht =>
    have value : eval cfg s (.bin .ne (.var "channels") (.cast .u64 (.lit 0))) = some (.integer 1) := by
      simp [eval, binary, loc.channels, show channels ≠ 0 by omega, show convert .u64 0 = 0 from rfl]
    rw [value] at he
    cases he
    contradiction
  | more he ht body rest =>
    rw [neon_tail_do_shape]
    exact .seq body (by simpa only [← neon_tail_loop_shape] using rest)

end Salty.Kernels.Rdsum
