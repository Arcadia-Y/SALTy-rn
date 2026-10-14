import Salty.Proofs.X32Pack.Headers
import Salty.Proofs.X32Pack.SpecLemmas

namespace Salty.Kernels.X32Pack
open CByte

/-- Permissions and input/output separation for one two-column tile. An odd
channel tile has one weight stream but still reserves two output columns. -/
structure TileSafe (m : Memory) (weights bias output : Address) (n : Nat) (paired : Bool) : Prop where
  weightsReadable : ∀ p, Footprint weights (4*n*(if paired then 2 else 1)) p → m.readable p = true
  biasReadable : bias ≠ 0 → ∀ p, Footprint bias (if paired then 8 else 4) p → m.readable p = true
  writable : ∀ p, Footprint output (8*(n+1)) p → m.writable p = true
  separate : ∀ p, Footprint weights (4*n*(if paired then 2 else 1)) p → ¬ Footprint output (8*(n+1)) p

theorem headerBytes_length (m : Memory) (bias : Address) (paired : Bool) :
    (headerBytes m bias paired).length ≤ 8 := by
  unfold headerBytes
  split <;> cases paired <;> simp

theorem TileSafe.header {m : Memory} {weights bias output : Address} {n : Nat} {paired : Bool}
    (safe : TileSafe m weights bias output n paired) : HeaderSafe m bias output paired := by
  exact ⟨safe.biasReadable, fun p hp => safe.writable p (footprint_mono (by omega) hp)⟩

theorem TileSafe.after_header {m : Memory} {weights bias output : Address} {n : Nat} {paired : Bool}
    (safe : TileSafe m weights bias output n paired) :
    PairSafe (writeBytes m output (headerBytes m bias paired)) weights
      (if paired then weights+BitVec.ofNat 64 (4*n) else weights) (output+8) n := by
  have left (p : Address) (hp : Footprint weights (4*n) p) :
      Footprint weights (4*n*(if paired then 2 else 1)) p := by
    apply footprint_mono _ hp
    cases paired <;> simp <;> omega
  have right (p : Address) (hp : Footprint (if paired then weights+BitVec.ofNat 64 (4*n) else weights) (4*n) p) :
      Footprint weights (4*n*(if paired then 2 else 1)) p := by
    cases paired with
    | false => simpa using hp
    | true => exact footprint_shift_within (by simp; omega) hp
  have out (p : Address) (hp : Footprint (output+8) (8*n) p) : Footprint output (8*(n+1)) p :=
    footprint_shift_within (start := 8) (by omega) hp
  constructor
  · intro p hp; simp only [writeBytes_readable]; exact safe.weightsReadable p (left p hp)
  · intro p hp; simp only [writeBytes_readable]; exact safe.weightsReadable p (right p hp)
  · intro p hp; simp only [writeBytes_writable]; exact safe.writable p (out p hp)
  · intro p hi ho; exact safe.separate p (left p hi) (out p ho)
  · intro p hi ho; exact safe.separate p (right p hi) (out p ho)

theorem TileSafe.header_preserves_weights {m : Memory} {weights bias output : Address} {n : Nat} {paired : Bool}
    (safe : TileSafe m weights bias output n paired) :
    readBytes (writeBytes m output (headerBytes m bias paired)) weights (4*n) = readBytes m weights (4*n) ∧
      readBytes (writeBytes m output (headerBytes m bias paired))
        (if paired then weights+BitVec.ofNat 64 (4*n) else weights) (4*n) =
      readBytes m (if paired then weights+BitVec.ofNat 64 (4*n) else weights) (4*n) := by
  have len := headerBytes_length m bias paired
  constructor <;> apply readBytes_writeBytes_disjoint <;> intro p hi ho
  · apply safe.separate p _ (footprint_mono (by omega) ho)
    apply footprint_mono _ hi
    cases paired <;> simp <;> omega
  · apply safe.separate p _ (footprint_mono (by omega) ho)
    cases paired with
    | false => simpa using hi
    | true => exact footprint_shift_within (by simp; omega) hi

theorem tile_pair_result {m : Memory} {weights bias output : Address} {n : Nat}
    (safe : TileSafe m weights bias output n true) :
    pairResult (writeBytes m output (headerBytes m bias true)) weights
      (weights+BitVec.ofNat 64 (4*n)) (output+8) n = writeTile m m weights bias output n true := by
  have reads := safe.header_preserves_weights
  simp only [Bool.true_eq, ↓reduceIte] at reads
  unfold pairResult pairBytes
  rw [reads.1, reads.2]
  rfl

theorem tile_single_result {m : Memory} {weights bias output : Address} {n : Nat}
    (safe : TileSafe m weights bias output n false) :
    singleResult (writeBytes m output (headerBytes m bias false)) weights (output+8) n =
      writeTile m m weights bias output n false := by
  have reads := safe.header_preserves_weights
  unfold singleResult
  rw [reads.1]
  rfl

@[simp] theorem writeTile_readable (original destination : Memory) (weights bias output : Address)
    (n : Nat) (paired : Bool) : (writeTile original destination weights bias output n paired).readable = destination.readable := by
  cases paired <;> simp [writeTile]

@[simp] theorem writeTile_writable (original destination : Memory) (weights bias output : Address)
    (n : Nat) (paired : Bool) : (writeTile original destination weights bias output n paired).writable = destination.writable := by
  cases paired <;> simp [writeTile]

/-- Includes the complete reserved tile in its frame; the sharper odd-lane
frame comes from singleResult_frame when composing the scalar depth path. -/
theorem writeTile_frame (original destination : Memory) (weights bias output p : Address)
    (n : Nat) (paired : Bool) (outside : ¬ Footprint output (8*(n+1)) p) :
    (writeTile original destination weights bias output n paired).data p = destination.data p := by
  have headerOut : ¬ Footprint output (headerBytes original bias paired).length p :=
    fun hp => outside (footprint_mono (by have := headerBytes_length original bias paired; omega) hp)
  have depthOut : ¬ Footprint (output+8) (8*n) p := fun hp => outside (footprint_shift_within (start := 8) (by omega) hp)
  cases paired with
  | false =>
    unfold writeTile
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [writeStrided32_frame _ _ _ _ _ _ (fun hp => depthOut (stride8_within _ _ _ hp))]
    exact writeBytes_frame _ _ _ _ headerOut
  | true =>
    unfold writeTile
    simp only [Bool.true_eq, ↓reduceIte]
    rw [writeBytes_frame _ _ _ _ (by simpa [interleaveWords_length] using depthOut)]
    exact writeBytes_frame _ _ _ _ headerOut

end Salty.Kernels.X32Pack
