import Salty.Spec.X32Pack
import Salty.Proofs.X32Pack.ChannelLayout

namespace Salty.Kernels.X32Pack
open CByte

/-- Remaining whole-group allocations. The footprint contracts are preserved
by completed groups, and the nonnull bias address cannot wrap between groups. -/
structure GroupSafe (m : Memory) (weights bias output : Address) (groups channels depth extra : Nat) : Prop where
  weightsReadable : ∀ p, Footprint weights (weightBytes channels depth*groups) p → m.readable p = true
  biasReadable : bias ≠ 0 → ∀ p, Footprint bias (4*channels*groups) p → m.readable p = true
  writable : ∀ p, Footprint output (groupBytes channels depth extra*groups) p → m.writable p = true
  weightsSeparate : ∀ p, Footprint weights (weightBytes channels depth*groups) p → ¬ Footprint output (groupBytes channels depth extra*groups) p
  biasSeparate : bias ≠ 0 → ∀ p, Footprint bias (4*channels*groups) p → ¬ Footprint output (groupBytes channels depth extra*groups) p
  biasBound : bias ≠ 0 → bias.toNat+4*channels*groups < 2^64

theorem GroupSafe.channel {m : Memory} {weights bias output : Address} {groups channels depth extra : Nat}
    (safe : GroupSafe m weights bias output groups channels depth extra) (positive : 0 < groups) :
    ChannelSafe m weights bias output channels depth extra := by
  have mul (a : Nat) : a ≤ a*groups := by
    have h := Nat.mul_le_mul_left a (show 1 ≤ groups by omega)
    simpa using h
  constructor
  · intro p hp; exact safe.weightsReadable p (footprint_mono (mul _) hp)
  · intro hn p hp; exact safe.biasReadable hn p (footprint_mono (mul _) hp)
  · intro p hp; exact safe.writable p (footprint_mono (mul _) hp)
  · intro p hi ho; exact safe.weightsSeparate p (footprint_mono (mul _) hi) (footprint_mono (mul _) ho)
  · intro hn p hi ho; exact safe.biasSeparate hn p (footprint_mono (mul _) hi) (footprint_mono (mul _) ho)
  · intro hn
    have h := safe.biasBound hn
    have b := mul (4*channels)
    omega

theorem GroupSafe.advance_group {m : Memory} {weights bias output : Address} {groups channels depth extra : Nat}
    (safe : GroupSafe m weights bias output (groups+1) channels depth extra) :
    GroupSafe (packChannels m weights bias output channels depth extra).memory
      (weights+BitVec.ofNat 64 (weightBytes channels depth)) (biasAdvance bias channels)
      (output+BitVec.ofNat 64 (groupBytes channels depth extra)) groups channels depth extra := by
  have weightsIn (p : Address) (hp : Footprint (weights+BitVec.ofNat 64 (weightBytes channels depth)) (weightBytes channels depth*groups) p) :
      Footprint weights (weightBytes channels depth*(groups+1)) p :=
    footprint_shift_within (by rw [Nat.mul_add, Nat.mul_one]; omega) hp
  have outputIn (p : Address) (hp : Footprint (output+BitVec.ofNat 64 (groupBytes channels depth extra)) (groupBytes channels depth extra*groups) p) :
      Footprint output (groupBytes channels depth extra*(groups+1)) p :=
    footprint_shift_within (by rw [Nat.mul_add, Nat.mul_one]; omega) hp
  have biasIn (p : Address) (hp : Footprint (bias+BitVec.ofNat 64 (4*channels)) (4*channels*groups) p) :
      Footprint bias (4*channels*(groups+1)) p :=
    footprint_shift_within (by rw [Nat.mul_add, Nat.mul_one]; omega) hp
  constructor
  · intro p hp; simp only [packChannels_readable]; exact safe.weightsReadable p (weightsIn p hp)
  · intro nonzero p hp
    simp only [packChannels_readable]
    by_cases zero : bias = 0#64
    · simp [biasAdvance, zero] at nonzero
    · simp [biasAdvance, zero] at hp
      exact safe.biasReadable zero p (biasIn p hp)
  · intro p hp; simp only [packChannels_writable]; exact safe.writable p (outputIn p hp)
  · intro p hi ho; exact safe.weightsSeparate p (weightsIn p hi) (outputIn p ho)
  · intro nonzero p hi ho
    by_cases zero : bias = 0#64
    · simp [biasAdvance, zero] at nonzero
    · simp [biasAdvance, zero] at hi
      exact safe.biasSeparate zero p (biasIn p hi) (outputIn p ho)
  · intro nonzero
    by_cases zero : bias = 0#64
    · simp [biasAdvance, zero] at nonzero
    · have total := safe.biasBound zero
      have small : bias.toNat+4*channels < 2^64 := by
        rw [Nat.mul_add, Nat.mul_one] at total
        omega
      rw [(biasAdvance_value zero small).1]
      rw [Nat.mul_add, Nat.mul_one] at total
      omega

theorem Entry.groupSafe {s : State} {c : Call} (entry : Entry s c) :
    GroupSafe s.memory c.weights c.bias c.output c.groups c.channels c.depth c.extra := by
  have weights : weightBytes c.channels c.depth*c.groups = 4*c.groups*c.channels*c.depth := by
    unfold weightBytes
    ac_rfl
  have output : groupBytes c.channels c.depth c.extra*c.groups = outputSize c := by
    unfold groupBytes outputSize
    ac_rfl
  have bias : 4*c.channels*c.groups = 4*c.groups*c.channels := by ac_rfl
  constructor
  · simpa only [weights] using entry.weightsReadable
  · simpa only [bias] using entry.biasReadable
  · simpa only [output] using entry.outputWritable
  · simpa only [weights, output] using entry.weightsSeparate
  · simpa only [bias, output] using entry.biasSeparate
  · simpa only [bias] using entry.biasBound

end Salty.Kernels.X32Pack
