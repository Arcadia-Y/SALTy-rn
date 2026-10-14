import Salty.Proofs.Rdsum.SpecLemmas

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- Convert the sequential byte reader to explicit original-memory column indices. -/
theorem readBytes_columns (m : Memory) (a : Address) (n : Nat) :
    readBytes m a n = (List.range n).map (fun i => m.data (a+BitVec.ofNat 64 i)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [readBytes, List.range_succ_eq_map, List.map_cons, List.map_map, ih]
    simp only [BitVec.add_zero, List.cons.injEq, true_and]
    apply List.map_congr_left
    intro i hi
    congr 1
    simp only [Function.comp_def, Nat.succ_eq_add_one, BitVec.ofNat_add]
    change a+1+BitVec.ofNat 64 i = a+(BitVec.ofNat 64 i+1)
    ac_rfl

theorem readBytes_constant (m : Memory) (a : Address) (n : Nat) (b : Byte)
    (same : ∀ p, Footprint a n p → m.data p = b) : readBytes m a n = List.replicate n b := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [readBytes, List.replicate_succ, same a ((footprint_succ a a n).mpr (.inl rfl))]
    congr 1
    exact ih (a+1) (fun p hp => same p ((footprint_succ a p n).mpr (.inr hp)))

/-- Live vector width is bounded by the remaining columns. The larger zero
allocation also covers the source's overlapping 16-byte loads. -/
theorem Entry.zero_load {kind : Interpretation} {s : State} {c : Call}
    (h : Entry kind s c) (n : Nat) (width : n ≤ max c.channels 40) :
    loadBytes s.memory c.zero n = some (List.replicate n 0) := by
  rw [loadBytes_success _ _ _ (fun p hp => h.zeroReadable p (footprint_mono width hp))]
  exact congrArg some (readBytes_constant _ _ _ _ (fun p hp => h.zeroContents p (footprint_mono width hp)))

/-- Any in-bounds strip of a live row is readable, including explicit source
padding. The arithmetic is modular; Entry separately excludes object wrap. -/
theorem Entry.row_load {kind : Interpretation} {s : State} {c : Call}
    (h : Entry kind s c) (row column width : Nat) (hr : row < c.rows)
    (hc : column+width ≤ c.channels+15) :
    loadBytes s.memory (c.input+BitVec.ofNat 64 (row*c.stride+column)) width =
      some (readBytes s.memory (c.input+BitVec.ofNat 64 (row*c.stride+column)) width) := by
  apply loadBytes_success
  intro a ha
  apply h.inputReadable row hr a
  apply footprint_shift_within hc
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using ha

theorem columnBytes_congr (m other : Memory) (input : Address) (stride rows column : Nat)
    (same : ∀ row, row < rows →
      m.data (input+BitVec.ofNat 64 (row*stride+column)) =
        other.data (input+BitVec.ofNat 64 (row*stride+column))) :
    columnBytes m input stride rows column = columnBytes other input stride rows column := by
  apply List.map_congr_left
  intro row hr
  exact same row (List.mem_range.mp hr)

/-- Separate output writes cannot alter any later input-column sum. -/
theorem Entry.column_preserved {kind : Interpretation} {s : State} {c : Call}
    (h : Entry kind s c) (bs : List Byte) (length : bs.length ≤ 4*c.channels)
    (column : Nat) (hc : column < c.channels) :
    columnSum kind (writeBytes s.memory c.output bs) c.input c.stride c.rows column =
      columnSum kind s.memory c.input c.stride c.rows column := by
  unfold columnSum
  congr 2
  apply columnBytes_congr
  intro row hr
  apply writeBytes_frame
  intro out
  apply h.inputSeparate row hr _ ?_ (footprint_mono length out)
  refine ⟨column,by omega,?_⟩
  simp only [BitVec.ofNat_add, BitVec.add_assoc]

end Salty.Kernels.Rdsum
