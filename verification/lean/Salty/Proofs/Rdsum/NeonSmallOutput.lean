import Salty.Proofs.Rdsum.NeonSmallMemory

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

private theorem low_bits (n : Nat) (small : n < 4) : n &&& 4 = 0 := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> decide

private theorem high_bits (n : Nat) (large : 4 ≤ n) (small : n < 8) :
    n &&& 4 ≠ 0 ∧ n &&& 2 = (n-4) &&& 2 ∧ n &&& 1 = (n-4) &&& 1 := by
  have cases : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> decide

/-- Every 0–7-channel output path uses exactly its required 4/2/1 stores. -/
theorem neon_small_output_exec (kind : Interpretation) (cfg : Config) (s : State) (output : Address)
    (low high : List (BitVec 32)) (ll : low.length = 4) (hl : high.length = 4)
    (channels : Nat) (small : channels < 8)
    (hc : s.locals "channels" = some (.integer channels))
    (out : s.locals "output" = some (.pointer output))
    (lo : s.locals "vacc0_2" = some (.words32 low))
    (hi : s.locals "vacc1" = some (.words32 high))
    (readable : ∀ a, Footprint output (4*channels) a → s.memory.readable a = true)
    (writable : ∀ a, Footprint output (4*channels) a → s.memory.writable a = true)
    (defined : LastOriginalDefined kind s.memory output (low++high) channels) :
    Exec cfg (branchNo (neonTailOutput kind)) s (smallStored s output low high channels) := by
  have shape : branchNo (neonTailOutput kind) = .seq (neonTailBranch kind 0) (neonLastStores kind) := by
    cases kind <;> rfl
  rw [shape]
  unfold smallStored
  split
  next fewer =>
    apply Exec.seq (tail_branch_no kind cfg s channels 0 (by omega) (by decide) hc
      (by simpa [tailBitMask] using low_bits channels fewer))
    exact neon_last_stores_exec kind cfg s output low ll channels channels (by omega) fewer rfl rfl hc out lo readable writable
      (last_defined_original kind s output low ll channels fewer (small_defined_low kind s output low high ll channels fewer defined))
  next more =>
    have large : 4 ≤ channels := by omega
    have bits := high_bits channels large small
    have four := neon_store4_exec kind cfg s output low high ll out lo hi
      (fun a ha => readable a (footprint_mono (by omega) ha))
      (fun a ha => writable a (footprint_mono (by omega) ha))
    apply Exec.seq (tail_branch_yes kind cfg s _ channels 0 (by omega) (by decide) hc
      (by simpa [tailBitMask] using bits.1) four)
    exact neon_last_stores_exec kind cfg (afterFour s output low high) (output+16) high hl
      channels (channels-4) (by omega) (by omega) bits.2.1 bits.2.2
      (by simp [afterFour, neonSmallStored, update, hc])
      (by simp [afterFour, neonSmallStored, update])
      (by simp [afterFour, neonSmallStored, update])
      (fun a ha => by
        simp only [afterFour, neonSmallStored, update, writeBytes_readable]
        exact readable a (footprint_shift_within (start := 16) (by omega) ha))
      (fun a ha => by
        simp only [afterFour, neonSmallStored, update, writeBytes_writable]
        exact writable a (footprint_shift_within (start := 16) (by omega) ha))
      (last_defined_original kind _ _ high hl (channels-4) (by omega)
        (small_defined_high kind s output low high ll hl channels large small defined))

end Salty.Kernels.Rdsum
