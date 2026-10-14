import Salty.Proofs.X32Pack.OddTile

namespace Salty.Kernels.X32Pack
open CByte

/-- Remaining channel region within a group. Bias and weights may alias each
other; both are separate from the entire remaining output region. -/
structure ChannelSafe (m : Memory) (weights bias output : Address) (channels depth extra : Nat) : Prop where
  weightsReadable : ∀ p, Footprint weights (4*depth*channels) p → m.readable p = true
  biasReadable : bias ≠ 0 → ∀ p, Footprint bias (4*channels) p → m.readable p = true
  writable : ∀ p, Footprint output (tiles channels*tileSize depth extra) p → m.writable p = true
  weightsSeparate : ∀ p, Footprint weights (4*depth*channels) p → ¬ Footprint output (tiles channels*tileSize depth extra) p
  biasSeparate : bias ≠ 0 → ∀ p, Footprint bias (4*channels) p → ¬ Footprint output (tiles channels*tileSize depth extra) p
  biasBound : bias ≠ 0 → bias.toNat+4*channels < 2^64

theorem tiles_add_two (n : Nat) : tiles (n+2) = tiles n+1 := by unfold tiles; omega

theorem ChannelSafe.pair {m : Memory} {weights bias output : Address} {channels depth extra : Nat}
    (safe : ChannelSafe m weights bias output channels depth extra) (count : 2 ≤ channels) :
    TileSafe m weights bias output depth true := by
  have weightBound : 4*depth*2 ≤ 4*depth*channels := Nat.mul_le_mul_left _ count
  have tileCount : 1 ≤ tiles channels := by unfold tiles; omega
  have outputBound : 8*(depth+1) ≤ tiles channels*tileSize depth extra := by
    have h := Nat.mul_le_mul_right (tileSize depth extra) tileCount
    simp only [Nat.one_mul] at h
    have base : 8*(depth+1) ≤ tileSize depth extra := by simp [tileSize]
    omega
  constructor
  · intro p hp; exact safe.weightsReadable p (footprint_mono weightBound hp)
  · intro hn p hp; exact safe.biasReadable hn p (footprint_mono (by simp; omega) hp)
  · intro p hp; exact safe.writable p (footprint_mono outputBound hp)
  · intro p hi ho; exact safe.weightsSeparate p (footprint_mono weightBound hi) (footprint_mono outputBound ho)

theorem ChannelSafe.odd {m : Memory} {weights bias output : Address} {depth extra : Nat}
    (safe : ChannelSafe m weights bias output 1 depth extra) : TileSafe m weights bias output depth false := by
  constructor
  · simpa using safe.weightsReadable
  · simpa using safe.biasReadable
  · intro p hp; exact safe.writable p (footprint_mono (by simp [tiles, tileSize]) hp)
  · intro p hi ho
    exact safe.weightsSeparate p (by simpa using hi) (footprint_mono (by simp [tiles, tileSize]) ho)

theorem bias_add_eight {bias : Address} {n : Nat} (bound : bias.toNat+4*(n+2) < 2^64) :
    (bias+8).toNat = bias.toNat+8 ∧ bias+8 ≠ 0#64 := by
  have small : bias.toNat+8 < 2^64 := by omega
  have value : (bias+8).toNat = bias.toNat+8 := by
    simp only [BitVec.toNat_add]
    change (bias.toNat+8)%2^64 = bias.toNat+8
    exact Nat.mod_eq_of_lt small
  refine ⟨value, ?_⟩
  intro zero
  have h := congrArg BitVec.toNat zero
  rw [value] at h
  simp at h

/-- Finishing a pair leaves the entire suffix readable/writable and disjoint.
This includes the optional bias pointer: a nonnull pointer cannot wrap to null. -/
theorem ChannelSafe.advance_pair {m : Memory} {weights bias output : Address} {n depth extra : Nat}
    (safe : ChannelSafe m weights bias output (n+2) depth extra) :
    ChannelSafe (writeTile m m weights bias output depth true)
      (weights+BitVec.ofNat 64 (8*depth)) (nextBias bias true)
      (output+BitVec.ofNat 64 (tileSize depth extra)) n depth extra := by
  have weightsIn (p : Address) (hp : Footprint (weights+BitVec.ofNat 64 (8*depth)) (4*depth*n) p) :
      Footprint weights (4*depth*(n+2)) p := footprint_shift_within (by simp [Nat.mul_add]; omega) hp
  have outputIn (p : Address) (hp : Footprint (output+BitVec.ofNat 64 (tileSize depth extra)) (tiles n*tileSize depth extra) p) :
      Footprint output (tiles (n+2)*tileSize depth extra) p := by
    apply footprint_shift_within _ hp
    rw [tiles_add_two, Nat.add_mul, Nat.one_mul]
    omega
  have biasIn (p : Address) (hp : Footprint (bias+8) (4*n) p) :
      Footprint bias (4*(n+2)) p := footprint_shift_within (start := 8) (by omega) hp
  constructor
  · intro p hp; simp only [writeTile_readable]; exact safe.weightsReadable p (weightsIn p hp)
  · intro nonzero p hp
    simp only [writeTile_readable]
    by_cases zero : bias = 0#64
    · simp [nextBias, zero] at nonzero
    · simp [nextBias, zero] at hp
      exact safe.biasReadable zero p (biasIn p hp)
  · intro p hp; simp only [writeTile_writable]; exact safe.writable p (outputIn p hp)
  · intro p hi ho; exact safe.weightsSeparate p (weightsIn p hi) (outputIn p ho)
  · intro nonzero p hi ho
    by_cases zero : bias = 0#64
    · simp [nextBias, zero] at nonzero
    · simp [nextBias, zero] at hi
      exact safe.biasSeparate zero p (biasIn p hi) (outputIn p ho)
  · intro nonzero
    by_cases zero : bias = 0#64
    · simp [nextBias, zero] at nonzero
    · have bound := safe.biasBound zero
      have value := (bias_add_eight bound).1
      simp [nextBias, zero, value]
      omega

end Salty.Kernels.X32Pack
