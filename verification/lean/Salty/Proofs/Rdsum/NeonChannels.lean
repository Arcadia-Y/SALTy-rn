import Salty.Proofs.Rdsum.NeonMainChannel

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def neonMainLoop (kind : Interpretation) : Stmt := firstStatement (dropStatements 5 (neonProgram kind))
def neonChannelLoops (kind : Interpretation) : Stmt := dropStatements 5 (neonProgram kind)

theorem neon_main_loop_shape (kind : Interpretation) : neonMainLoop kind =
    .loop (.bin .ge (.var "channels") (.cast .u64 (.lit (neonWidth kind true)))) (neonMainChannelIteration kind) := by
  cases kind <;> rfl

theorem neon_channel_loops_shape (kind : Interpretation) : neonChannelLoops kind =
    .seq (neonMainLoop kind) (.seq (neonTail kind) .skip) := by cases kind <;> rfl

/-- Unbounded main-channel iterations followed by the actual guarded tail,
including the source's padded-load and signed-scalar-definedness obligations. -/
theorem neon_channels_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero output : Address) (rows stride channels : Nat)
    (rowBound : rows < 2^31) (strideBound : 7*stride < 2^64) (channelBound : channels < 2^64)
    (loc : ChannelLocals s rows channels stride input zero output)
    (safe : NeonSafe kind s.memory input zero output rows stride channels) :
    ∃ t, Exec cfg (neonChannelLoops kind) s t ∧
      t.memory = writeBytes s.memory output (encodeWords32 (stripWords kind s.memory input output rows stride channels)) ∧
      t.locals "channels" = some (.integer 0) := by
  induction channels using Nat.strongRecOn generalizing s input output with
  | ind channels ih =>
    have castWidth : convert .u64 (neonWidth kind true) = (neonWidth kind true : Int) := by cases kind <;> rfl
    by_cases large : neonWidth kind true ≤ channels
    · have widthPositive : 0 < neonWidth kind true := by cases kind <;> decide
      obtain ⟨u,body,mem,uloc⟩ := neon_main_channel_correct kind cfg s input zero output rows stride channels rowBound channelBound large loc safe
      have nextSafe : NeonSafe kind u.memory (input+BitVec.ofNat 64 (neonWidth kind true)) zero
          (output+BitVec.ofNat 64 (4*neonWidth kind true)) rows stride (channels-neonWidth kind true) := by
        rw [mem]
        exact safe.advance large (by cases kind <;> decide) _ (by simp [stripWords])
      obtain ⟨t,rest,tmem,done⟩ := ih (channels-neonWidth kind true) (by omega) u _ _ (by omega) uloc nextSafe
      refine ⟨t,?_,?_,done⟩
      · rw [neon_channel_loops_shape] at rest ⊢
        cases rest with
        | seq loop tail =>
          apply Exec.seq (t := _) ?_ tail
          rw [neon_main_loop_shape] at loop ⊢
          apply Exec.more (v := .integer 1) (t := u)
          · simp [eval, binary, loc.channels, castWidth, show (neonWidth kind true : Int) ≤ channels by omega]
          · rfl
          · exact body
          · exact loop
      · rw [tmem,mem]
        exact strip_write_join kind s.memory input zero output rows stride channels (neonWidth kind true) safe.toChannelSafe large
    · obtain ⟨t,tail,mem,done⟩ := neon_tail_correct kind cfg s input zero output rows stride channels rowBound strideBound (by omega) loc safe
      refine ⟨t,?_,mem,done⟩
      rw [neon_channel_loops_shape]
      apply Exec.seq (t := s) ?_ (.seq tail .skip)
      rw [neon_main_loop_shape]
      apply Exec.done (v := .integer 0)
      · simp [eval, binary, loc.channels, castWidth, show ¬ (neonWidth kind true : Int) ≤ channels by omega]
      · rfl

end Salty.Kernels.Rdsum
