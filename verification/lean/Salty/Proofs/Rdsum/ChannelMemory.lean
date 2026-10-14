import Salty.Proofs.Rdsum.ChannelSafety

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

@[simp] theorem stripWords_length (kind : Interpretation) (m : Memory) (input output : Address)
    (rows stride width : Nat) : (stripWords kind m input output rows stride width).length = width := by
  simp [stripWords]

theorem columnSum_shift (kind : Interpretation) (m : Memory) (input : Address)
    (stride rows start column : Nat) :
    columnSum kind m (input+BitVec.ofNat 64 start) stride rows column =
      columnSum kind m input stride rows (start+column) := by
  unfold columnSum
  congr 2
  apply List.map_congr_left
  intro row hr
  congr 1
  simp only [BitVec.ofNat_add, BitVec.add_assoc]
  ac_rfl

theorem stripWords_add (kind : Interpretation) (m : Memory) (input output : Address)
    (rows stride left right : Nat) :
    stripWords kind m input output rows stride (left+right) =
      stripWords kind m input output rows stride left ++
      stripWords kind m (input+BitVec.ofNat 64 left) (output+BitVec.ofNat 64 (4*left)) rows stride right := by
  simp only [stripWords, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_def, columnSum_shift]
  congr 2
  simp only [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

theorem encodeWords32_append (xs ys : List (BitVec 32)) :
    encodeWords32 (xs++ys) = encodeWords32 xs++encodeWords32 ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords32, ih, List.append_assoc]

/-- A completed prefix cannot change any later input column or old output word.
Output-prefix/suffix separation follows from the finite address-space bound. -/
theorem stripWords_after_prefix (kind : Interpretation) (m : Memory) (input zero output : Address)
    (rows stride channels width : Nat) (safe : ChannelSafe m input zero output rows stride channels)
    (within : width ≤ channels) (bs : List Byte) (len : bs.length = 4*width) :
    stripWords kind (writeBytes m output bs) (input+BitVec.ofNat 64 width)
      (output+BitVec.ofNat 64 (4*width)) rows stride (channels-width) =
    stripWords kind m (input+BitVec.ofNat 64 width)
      (output+BitVec.ofNat 64 (4*width)) rows stride (channels-width) := by
  unfold stripWords
  apply List.map_congr_left
  intro column hc
  have col : column < channels-width := List.mem_range.mp hc
  have read : readWord32 (writeBytes m output bs)
      (output+BitVec.ofNat 64 (4*width)+BitVec.ofNat 64 (4*column)) =
      readWord32 m (output+BitVec.ofNat 64 (4*width)+BitVec.ofNat 64 (4*column)) := by
    unfold readWord32
    rw [readBytes_writeBytes_disjoint]
    intro a ha
    rw [len]
    apply footprint_prefix_suffix output a (4*width) (4*(channels-width)) (by have := safe.outSize; omega)
    exact footprint_shift_within (by omega) ha
  rw [read]
  congr 1
  unfold columnSum
  congr 2
  apply columnBytes_congr
  intro row hr
  apply writeBytes_frame
  intro ho
  apply safe.inputSeparate row hr _ ?_ (footprint_mono (by omega) ho)
  refine ⟨width+column,by omega,?_⟩
  simp only [BitVec.ofNat_add, BitVec.add_assoc]
  ac_rfl

/-- Sequential stores of adjacent strips equal the one-shot scalar result. -/
theorem strip_write_join (kind : Interpretation) (m : Memory) (input zero output : Address)
    (rows stride channels width : Nat) (safe : ChannelSafe m input zero output rows stride channels)
    (within : width ≤ channels) :
    let first := encodeWords32 (stripWords kind m input output rows stride width);
    let next := writeBytes m output first;
    writeBytes next (output+BitVec.ofNat 64 (4*width))
      (encodeWords32 (stripWords kind next (input+BitVec.ofNat 64 width)
        (output+BitVec.ofNat 64 (4*width)) rows stride (channels-width))) =
    writeBytes m output (encodeWords32 (stripWords kind m input output rows stride channels)) := by
  dsimp only
  rw [stripWords_after_prefix kind m input zero output rows stride channels width safe within _ (by simp)]
  have split : channels = width+(channels-width) := by omega
  conv => rhs; rw [split, stripWords_add, encodeWords32_append, writeBytes_append]
  simp only [encodeWords32_length, stripWords_length]

end Salty.Kernels.Rdsum
