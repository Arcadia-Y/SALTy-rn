import Salty.Proofs.Rdsum.NeonSmallOutput

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

def tailOutputAfter (s : State) (input output : Address) (low high : List (BitVec 32)) (channels : Nat) : State :=
  if 8 ≤ channels then neonAdvanced8 (neonStored8 s output low high) input channels
  else smallStored s output low high channels

theorem neon_tail_output_shape (kind : Interpretation) : neonTailOutput kind =
    .branch (.bin .ge (.var "channels") (.cast .u64 (.lit 8)))
      (branchYes (neonTailOutput kind)) (branchNo (neonTailOutput kind)) := by
  cases kind <;> rfl

theorem neon_tail_output_exec (kind : Interpretation) (cfg : Config) (s : State) (input output : Address)
    (low high : List (BitVec 32)) (ll : low.length = 4) (hl : high.length = 4)
    (channels : Nat) (bound : channels < 2^64)
    (hc : s.locals "channels" = some (.integer channels))
    (hin : s.locals "input" = some (.pointer input))
    (out : s.locals "output" = some (.pointer output))
    (lo : s.locals "vacc0_2" = some (.words32 low))
    (hi : s.locals "vacc1" = some (.words32 high))
    (readable : ∀ a, Footprint output (4*min channels 8) a → s.memory.readable a = true)
    (writable : ∀ a, Footprint output (4*min channels 8) a → s.memory.writable a = true)
    (defined : channels < 8 → LastOriginalDefined kind s.memory output (low++high) channels) :
    Exec cfg (neonTailOutput kind) s (tailOutputAfter s input output low high channels) := by
  rw [neon_tail_output_shape]
  unfold tailOutputAfter
  split
  next large =>
    apply Exec.yes (v := .integer 1)
    · simp [eval, binary, hc, show convert .u64 8 = 8 from rfl, show (8 : Int) ≤ channels by omega]
    · rfl
    · exact neon_output8_exec kind cfg s input output channels bound large low high ll hl hin hc out lo hi
        (by simpa only [Nat.min_eq_right large] using readable)
        (by simpa only [Nat.min_eq_right large] using writable)
  next small =>
    apply Exec.no (v := .integer 0)
    · simp [eval, binary, hc, show convert .u64 8 = 8 from rfl, show ¬(8 : Int) ≤ channels by omega]
    · rfl
    · exact neon_small_output_exec kind cfg s output low high ll hl channels (by omega) hc out lo hi
        (by simpa only [Nat.min_eq_left (by omega : channels ≤ 8)] using readable)
        (by simpa only [Nat.min_eq_left (by omega : channels ≤ 8)] using writable) (defined (by omega))

theorem tailOutputAfter_memory (s : State) (input output : Address) (low high : List (BitVec 32))
    (ll : low.length = 4) (hl : high.length = 4) (channels : Nat) :
    (tailOutputAfter s input output low high channels).memory =
      writeBytes s.memory output
        (encodeWords32 (storedWords s.memory output (min channels 8) ((low++high).take (min channels 8)))) := by
  unfold tailOutputAfter
  split
  next large =>
    have take : (low++high).take 8 = low++high := List.take_of_length_le (by simp [ll,hl])
    simp only [neonAdvanced8, update, neonStored8_memory s output low high ll hl,
      Nat.min_eq_right large, take]
  next small =>
    rw [smallStored_memory s output low high ll hl channels (by omega), Nat.min_eq_left (by omega)]

theorem tailOutputAfter_locals (s : State) (input zero output : Address) (low high : List (BitVec 32))
    (rows channels stride : Nat) (loc : ChannelLocals s rows channels stride input zero output) :
    if 8 ≤ channels then
      ChannelLocals (tailOutputAfter s input output low high channels) rows (channels-8) stride (input+8) zero (output+32)
    else (tailOutputAfter s input output low high channels).locals "channels" = some (.integer 0) := by
  split
  next large =>
    simp only [tailOutputAfter, if_pos large]
    constructor <;> simp [neonAdvanced8, neonStored8, update, BitVec.add_assoc,
      loc.rows, loc.strideLocal, loc.zero, loc.increment]
  next small => simp [tailOutputAfter, small]

end Salty.Kernels.Rdsum
