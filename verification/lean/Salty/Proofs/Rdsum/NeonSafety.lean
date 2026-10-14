import Salty.Proofs.Rdsum.NeonTailChannel

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

def ScalarColumnDefined (kind : Interpretation) (m : Memory) (input output : Address)
    (rows stride channels : Nat) : Prop :=
  channels % 2 = 1 → ScalarStoreDefined kind
    (readWord32 m (output+BitVec.ofNat 64 (4*(channels-1))))
    (columnSum kind m input stride rows (channels-1))

/-- NEON additionally reads fixed-width tails, so the padding and zero-buffer
separation must survive each completed strip. -/
structure NeonSafe (kind : Interpretation) (m : Memory) (input zero output : Address)
    (rows stride channels : Nat) : Prop extends ChannelSafe m input zero output rows stride channels where
  inputPadRead : ∀ row, row < rows → ∀ a,
    Footprint (input+BitVec.ofNat 64 (row*stride)) (channels+15) a → m.readable a = true
  zeroPadRead : ∀ a, Footprint zero 40 a → m.readable a = true
  zeroPadContents : ∀ a, Footprint zero 40 a → m.data a = 0
  inputPadSeparate : ∀ row, row < rows → ∀ a,
    Footprint (input+BitVec.ofNat 64 (row*stride)) (channels+15) a → ¬ Footprint output (4*channels) a
  zeroPadSeparate : ∀ a, Footprint zero 40 a → ¬ Footprint output (4*channels) a
  scalarDefined : ScalarColumnDefined kind m input output rows stride channels

theorem columnSum_after_prefix (kind : Interpretation) (m : Memory) (input zero output : Address)
    (rows stride channels width column : Nat) (safe : ChannelSafe m input zero output rows stride channels)
    (within : width ≤ channels) (col : column < channels-width) (bs : List Byte) (len : bs.length = 4*width) :
    columnSum kind (writeBytes m output bs) (input+BitVec.ofNat 64 width) stride rows column =
      columnSum kind m input stride rows (width+column) := by
  rw [columnSum_shift]
  unfold columnSum
  congr 2
  apply columnBytes_congr
  intro row hr
  apply writeBytes_frame
  intro ho
  apply safe.inputSeparate row hr _ ?_ (footprint_mono (by omega) ho)
  refine ⟨width+column,by omega,?_⟩
  simp only [BitVec.ofNat_add, BitVec.add_assoc]

theorem ScalarColumnDefined.advance {kind : Interpretation} {m : Memory} {input zero output : Address}
    {rows stride channels width : Nat} (defined : ScalarColumnDefined kind m input output rows stride channels)
    (safe : ChannelSafe m input zero output rows stride channels) (within : width ≤ channels) (even : width % 2 = 0)
    (bs : List Byte) (len : bs.length = 4*width) :
    ScalarColumnDefined kind (writeBytes m output bs) (input+BitVec.ofNat 64 width)
      (output+BitVec.ofNat 64 (4*width)) rows stride (channels-width) := by
  intro odd
  have oldOdd : channels % 2 = 1 := by omega
  have positive : 0 < channels-width := by omega
  have index : width+(channels-width-1) = channels-1 := by omega
  have read := readWord32_after_prefix_at m output width (channels-width-1) bs len
    (by have := safe.outSize; omega)
  rw [read, columnSum_after_prefix kind m input zero output rows stride channels width (channels-width-1) safe within (by omega) bs len, index]
  have address : output+BitVec.ofNat 64 (4*width)+BitVec.ofNat 64 (4*(channels-width-1)) =
      output+BitVec.ofNat 64 (4*(channels-1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add, index]
  rw [address]
  exact defined oldOdd

theorem NeonSafe.advance {kind : Interpretation} {m : Memory} {input zero output : Address}
    {rows stride channels width : Nat} (safe : NeonSafe kind m input zero output rows stride channels)
    (within : width ≤ channels) (even : width % 2 = 0) (bs : List Byte) (len : bs.length = 4*width) :
    NeonSafe kind (writeBytes m output bs) (input+BitVec.ofNat 64 width) zero
      (output+BitVec.ofNat 64 (4*width)) rows stride (channels-width) := by
  have outIn (a : Address) (h : Footprint (output+BitVec.ofNat 64 (4*width)) (4*(channels-width)) a) :
      Footprint output (4*channels) a := footprint_shift_within (by omega) h
  have rowIn (row : Nat) (a : Address)
      (h : Footprint (input+BitVec.ofNat 64 width+BitVec.ofNat 64 (row*stride)) (channels-width+15) a) :
      Footprint (input+BitVec.ofNat 64 (row*stride)) (channels+15) a := by
    apply shifted_row_footprint input a row stride (channels+15) width (by omega)
    simpa only [show channels+15-width = channels-width+15 by omega] using h
  constructor
  · exact safe.toChannelSafe.advance within bs len
  · intro row hr a ha
    simp only [writeBytes_readable]
    exact safe.inputPadRead row hr a (rowIn row a ha)
  · intro a ha
    simp only [writeBytes_readable]
    exact safe.zeroPadRead a ha
  · intro a ha
    rw [writeBytes_frame]
    · exact safe.zeroPadContents a ha
    · intro ho
      exact safe.zeroPadSeparate a ha (footprint_mono (by omega) ho)
  · intro row hr a hi ho
    exact safe.inputPadSeparate row hr a (rowIn row a hi) (outIn a ho)
  · intro a hi ho
    exact safe.zeroPadSeparate a hi (outIn a ho)
  · exact safe.scalarDefined.advance safe.toChannelSafe within even bs len

theorem Entry.neon_safe {kind : Interpretation} {s : State} {c : Call} (entry : Entry kind s c) :
    NeonSafe kind s.memory c.input c.zero c.output c.rows c.stride c.channels := by
  constructor
  · exact entry.channel_safe
  · exact entry.inputReadable
  · intro a ha; exact entry.zeroReadable a (footprint_mono (Nat.le_max_right ..) ha)
  · intro a ha; exact entry.zeroContents a (footprint_mono (Nat.le_max_right ..) ha)
  · exact entry.inputSeparate
  · intro a ha; exact entry.zeroSeparate a (footprint_mono (Nat.le_max_right ..) ha)
  · cases kind with
    | signed => exact entry.scalarDefined
    | unsigned => intro _; trivial

theorem ScalarColumnDefined.tail {kind : Interpretation} {m : Memory} {input output : Address}
    {rows stride channels : Nat} (defined : ScalarColumnDefined kind m input output rows stride channels)
    (small : channels < 8) :
    LastOriginalDefined kind m output (tailValues kind m input stride rows) channels := by
  intro odd
  have index : channels-1 < 8 := by omega
  simpa [tailValues, List.getElem!_eq_getElem?_getD, index] using defined odd

end Salty.Kernels.Rdsum
