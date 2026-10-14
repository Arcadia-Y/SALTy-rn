import Salty.Proofs.Rdsum.RvvChannel

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- Storage for the remaining columns. The zero buffer is reused from its
base on every iteration; input rows may overlap, but output is separate. -/
structure ChannelSafe (m : Memory) (input zero output : Address) (rows stride channels : Nat) : Prop where
  inputRead : ∀ row, row < rows → ∀ a,
    Footprint (input+BitVec.ofNat 64 (row*stride)) channels a → m.readable a = true
  zeroRead : ∀ a, Footprint zero channels a → m.readable a = true
  zeros : ∀ a, Footprint zero channels a → m.data a = 0
  outRead : ∀ a, Footprint output (4*channels) a → m.readable a = true
  outWrite : ∀ a, Footprint output (4*channels) a → m.writable a = true
  inputSeparate : ∀ row, row < rows → ∀ a,
    Footprint (input+BitVec.ofNat 64 (row*stride)) channels a → ¬ Footprint output (4*channels) a
  zeroSeparate : ∀ a, Footprint zero channels a → ¬ Footprint output (4*channels) a
  outSize : 4*channels < 2^64

theorem footprint_prefix_suffix (a p : Address) (left right : Nat) (bound : left+right < 2^64)
    (suffix : Footprint (a+BitVec.ofNat 64 left) right p) : ¬ Footprint a left p := by
  rintro ⟨i,hi,pi⟩
  obtain ⟨j,hj,pj⟩ := suffix
  have eq := pi.symm.trans pj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add] at eq
  have nat := congrArg BitVec.toNat ((BitVec.add_right_inj a).mp eq)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega),
    Nat.mod_eq_of_lt (show left+j < 2^64 by omega)] at nat
  omega

theorem shifted_row_footprint (input p : Address) (row stride channels width : Nat)
    (within : width ≤ channels)
    (h : Footprint (input+BitVec.ofNat 64 width+BitVec.ofNat 64 (row*stride)) (channels-width) p) :
    Footprint (input+BitVec.ofNat 64 (row*stride)) channels p := by
  apply footprint_shift_within (start := width) (count := channels-width) (by omega)
  have eq : input+BitVec.ofNat 64 width+BitVec.ofNat 64 (row*stride) =
      input+BitVec.ofNat 64 (row*stride)+BitVec.ofNat 64 width := by ac_rfl
  simpa only [eq] using h

theorem ChannelSafe.advance {m : Memory} {input zero output : Address} {rows stride channels width : Nat}
    (safe : ChannelSafe m input zero output rows stride channels) (within : width ≤ channels)
    (bs : List Byte) (len : bs.length = 4*width) :
    ChannelSafe (writeBytes m output bs) (input+BitVec.ofNat 64 width) zero
      (output+BitVec.ofNat 64 (4*width)) rows stride (channels-width) := by
  have outIn (a : Address) (h : Footprint (output+BitVec.ofNat 64 (4*width)) (4*(channels-width)) a) :
      Footprint output (4*channels) a := footprint_shift_within (by omega) h
  constructor
  · intro row hr a ha
    simp only [writeBytes_readable]
    exact safe.inputRead row hr a (shifted_row_footprint input a row stride channels width within ha)
  · intro a ha
    simp only [writeBytes_readable]
    exact safe.zeroRead a (footprint_mono (by omega) ha)
  · intro a ha
    rw [writeBytes_frame]
    · exact safe.zeros a (footprint_mono (by omega) ha)
    · intro ho
      exact safe.zeroSeparate a (footprint_mono (by omega) ha) (footprint_mono (by omega) ho)
  · intro a ha
    simp only [writeBytes_readable]
    exact safe.outRead a (outIn a ha)
  · intro a ha
    simp only [writeBytes_writable]
    exact safe.outWrite a (outIn a ha)
  · intro row hr a hi ho
    exact safe.inputSeparate row hr a (shifted_row_footprint input a row stride channels width within hi) (outIn a ho)
  · intro a hi ho
    exact safe.zeroSeparate a (footprint_mono (by omega) hi) (outIn a ho)
  · have := safe.outSize; omega

theorem Entry.channel_safe {kind : Interpretation} {s : State} {c : Call} (entry : Entry kind s c) :
    ChannelSafe s.memory c.input c.zero c.output c.rows c.stride c.channels := by
  constructor
  · intro row hr a ha; exact entry.inputReadable row hr a (footprint_mono (by omega) ha)
  · intro a ha; exact entry.zeroReadable a (footprint_mono (by omega) ha)
  · intro a ha; exact entry.zeroContents a (footprint_mono (by omega) ha)
  · exact entry.outputReadable
  · exact entry.outputWritable
  · intro row hr a ha; exact entry.inputSeparate row hr a (footprint_mono (by omega) ha)
  · intro a ha; exact entry.zeroSeparate a (footprint_mono (by omega) ha)
  · have := entry.outputBound; omega

end Salty.Kernels.Rdsum
