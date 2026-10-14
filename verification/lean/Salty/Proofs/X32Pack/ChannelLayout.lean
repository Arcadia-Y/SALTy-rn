import Salty.Spec.X32Pack
import Salty.Proofs.X32Pack.Channels

namespace Salty.Kernels.X32Pack
open CByte

@[simp] theorem packPairs_readable (depth extra pairs : Nat) (m : Memory) (weights bias output : Address) :
    (packPairs depth extra pairs m weights bias output).memory.readable = m.readable := by
  induction pairs generalizing m weights bias output with
  | zero => rfl
  | succ pairs ih => simp only [packPairs, ih, writeTile_readable]

@[simp] theorem packPairs_writable (depth extra pairs : Nat) (m : Memory) (weights bias output : Address) :
    (packPairs depth extra pairs m weights bias output).memory.writable = m.writable := by
  induction pairs generalizing m weights bias output with
  | zero => rfl
  | succ pairs ih => simp only [packPairs, ih, writeTile_writable]

theorem packPairs_weights (depth extra pairs : Nat) (m : Memory) (weights bias output : Address) :
    (packPairs depth extra pairs m weights bias output).weights = weights+BitVec.ofNat 64 (8*depth*pairs) := by
  induction pairs generalizing m weights bias output with
  | zero => simp [packPairs]
  | succ pairs ih =>
    simp only [packPairs, ih]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    rw [Nat.mul_succ]
    omega

theorem packPairs_output (depth extra pairs : Nat) (m : Memory) (weights bias output : Address) :
    (packPairs depth extra pairs m weights bias output).output = output+BitVec.ofNat 64 (pairs*tileSize depth extra) := by
  induction pairs generalizing m weights bias output with
  | zero => simp [packPairs]
  | succ pairs ih =>
    simp only [packPairs, ih]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    rw [Nat.succ_mul]
    omega

theorem packPairs_bias (depth extra pairs : Nat) (m : Memory) (weights bias output : Address)
    (bound : bias ≠ 0 → bias.toNat+8*pairs < 2^64) :
    (packPairs depth extra pairs m weights bias output).bias = biasAdvance bias (2*pairs) := by
  induction pairs generalizing m weights bias output with
  | zero => by_cases zero : bias = 0#64 <;> simp [packPairs, biasAdvance, zero]
  | succ pairs ih =>
    by_cases zero : bias = 0#64
    · subst bias
      simp only [packPairs]
      rw [ih _ _ _ _ (by simp [nextBias])]
      simp [nextBias, biasAdvance]
    · have large := bound zero
      have stepBound : bias.toNat+4*(2*pairs+2) < 2^64 := by omega
      obtain ⟨value, nonzero⟩ := bias_add_eight stepBound
      have nextBound : nextBias bias true ≠ 0 → (nextBias bias true).toNat+8*pairs < 2^64 := by
        intro _
        simp [nextBias, zero, value]
        omega
      simp only [packPairs]
      rw [ih _ _ _ _ nextBound]
      have nz : bias+8#64 ≠ 0#64 := nonzero
      simp [biasAdvance, nextBias, zero, nz]
      rw [BitVec.add_assoc]
      change bias+(BitVec.ofNat 64 8+BitVec.ofNat 64 (4*(2*pairs))) = _
      rw [← BitVec.ofNat_add]
      congr 2
      omega

@[simp] theorem packChannels_readable (m : Memory) (weights bias output : Address) (channels depth extra : Nat) :
    (packChannels m weights bias output channels depth extra).memory.readable = m.readable := by
  unfold packChannels
  split <;> simp [oddResult]

@[simp] theorem packChannels_writable (m : Memory) (weights bias output : Address) (channels depth extra : Nat) :
    (packChannels m weights bias output channels depth extra).memory.writable = m.writable := by
  unfold packChannels
  split <;> simp [oddResult]

theorem packChannels_weights (m : Memory) (weights bias output : Address) (channels depth extra : Nat) :
    (packChannels m weights bias output channels depth extra).weights = weights+BitVec.ofNat 64 (4*depth*channels) := by
  unfold packChannels
  split
  · rename_i even
    rw [packPairs_weights]
    congr 2
    have count : channels = 2*(channels/2) := by omega
    rw [show 8*depth = (4*depth)*2 by omega, Nat.mul_assoc, ← count]
  · rename_i odd
    simp only [oddResult, packPairs_weights]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    have count : channels = 2*(channels/2)+1 := by omega
    calc
      8*depth*(channels/2)+4*depth = (4*depth)*(2*(channels/2)+1) := by
        rw [Nat.mul_add, Nat.mul_one, show 8*depth = (4*depth)*2 by omega, Nat.mul_assoc]
      _ = 4*depth*channels := by rw [← count]

theorem packChannels_output (m : Memory) (weights bias output : Address) (channels depth extra : Nat) :
    (packChannels m weights bias output channels depth extra).output = output+BitVec.ofNat 64 (tiles channels*tileSize depth extra) := by
  unfold packChannels
  split
  · rename_i even
    rw [packPairs_output]
    congr 2
    have count : tiles channels = channels/2 := by unfold tiles; omega
    rw [count]
  · rename_i odd
    simp only [oddResult, packPairs_output]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    have count : tiles channels = channels/2+1 := by unfold tiles; omega
    rw [count, Nat.add_mul, Nat.one_mul]

theorem biasAdvance_value {bias : Address} {n : Nat} (nonzero : bias ≠ 0#64)
    (bound : bias.toNat+4*n < 2^64) :
    (biasAdvance bias n).toNat = bias.toNat+4*n ∧ biasAdvance bias n ≠ 0#64 := by
  have small : 4*n < 2^64 := by omega
  have value : (biasAdvance bias n).toNat = bias.toNat+4*n := by
    simp [biasAdvance, nonzero, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt bound]
  have nz : bias.toNat ≠ 0 := by
    intro h
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    exact h
  refine ⟨value, ?_⟩
  intro h
  have zero := congrArg BitVec.toNat h
  rw [value] at zero
  change bias.toNat+4*n = 0 at zero
  omega

theorem biasAdvance_add (bias : Address) (a b : Nat)
    (bound : bias ≠ 0 → bias.toNat+4*(a+b) < 2^64) :
    biasAdvance (biasAdvance bias a) b = biasAdvance bias (a+b) := by
  by_cases zero : bias = 0#64
  · simp [biasAdvance, zero]
  · have total := bound zero
    have nz := (biasAdvance_value zero (show bias.toNat+4*a < 2^64 by omega)).2
    unfold biasAdvance at nz ⊢
    simp [zero] at nz ⊢
    rw [if_neg nz, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]

theorem packChannels_bias (m : Memory) (weights bias output : Address) (channels depth extra : Nat)
    (bound : bias ≠ 0 → bias.toNat+4*channels < 2^64) :
    (packChannels m weights bias output channels depth extra).bias = biasAdvance bias channels := by
  have pairBound : bias ≠ 0 → bias.toNat+8*(channels/2) < 2^64 := by
    intro nonzero
    have h := bound nonzero
    omega
  unfold packChannels
  split
  · rename_i even
    rw [packPairs_bias _ _ _ _ _ _ _ pairBound]
    have count : 2*(channels/2) = channels := by omega
    rw [count]
  · rename_i odd
    simp only [oddResult]
    rw [packPairs_bias _ _ _ _ _ _ _ pairBound]
    have next (p : Address) : nextBias p false = biasAdvance p 1 := rfl
    rw [next]
    have count : 2*(channels/2)+1 = channels := by omega
    rw [biasAdvance_add bias (2*(channels/2)) 1 (by rw [count]; exact bound), count]

theorem packPairs_frame (depth extra pairs : Nat) (m : Memory) (weights bias output p : Address)
    (outside : ¬ Footprint output (pairs*tileSize depth extra) p) :
    (packPairs depth extra pairs m weights bias output).memory.data p = m.data p := by
  induction pairs generalizing m weights bias output with
  | zero => rfl
  | succ pairs ih =>
    have suffixOut : ¬ Footprint (output+BitVec.ofNat 64 (tileSize depth extra)) (pairs*tileSize depth extra) p := by
      intro hp
      apply outside
      exact footprint_shift_within (by rw [Nat.succ_mul]; omega) hp
    have tileOut : ¬ Footprint output (8*(depth+1)) p := by
      intro hp
      apply outside
      apply footprint_mono _ hp
      have h := Nat.mul_le_mul_right (tileSize depth extra) (show 1 ≤ pairs+1 by omega)
      simp only [Nat.one_mul] at h
      have tileBound : 8*(depth+1) ≤ tileSize depth extra := by simp [tileSize]
      exact Nat.le_trans tileBound h
    simp only [packPairs]
    rw [ih _ _ _ _ suffixOut, writeTile_frame _ _ _ _ _ _ _ _ tileOut]

theorem packChannels_frame (m : Memory) (weights bias output p : Address) (channels depth extra : Nat)
    (outside : ¬ Footprint output (tiles channels*tileSize depth extra) p) :
    (packChannels m weights bias output channels depth extra).memory.data p = m.data p := by
  have pairOut : ¬ Footprint output ((channels/2)*tileSize depth extra) p := by
    intro hp
    apply outside
    exact footprint_mono (Nat.mul_le_mul_right _ (by unfold tiles; omega)) hp
  unfold packChannels
  split
  · exact packPairs_frame _ _ _ _ _ _ _ _ pairOut
  · rename_i odd
    simp only [oddResult]
    rw [writeTile_frame]
    · exact packPairs_frame _ _ _ _ _ _ _ _ pairOut
    · rw [packPairs_output]
      intro hp
      apply outside
      apply footprint_shift_within _ hp
      have count : tiles channels = channels/2+1 := by unfold tiles; omega
      rw [count, Nat.add_mul, Nat.one_mul]
      have tileBound : 8*(depth+1) ≤ tileSize depth extra := by simp [tileSize]
      omega

end Salty.Kernels.X32Pack
