import Salty.Proofs.X32Transpose.Safety
import Salty.Proofs.X32Transpose.NeonMatrix

namespace Salty.Kernels.X32Transpose
open CByte

/-- The source always loads two words, including a padded word on a one-column
strip. Every padded input byte is separate from all actual output words. -/
structure NeonStripSafe (m : Memory) (p : MatrixCopy) : Prop where
  common : RowsSafe m p.input p.output p.inputStride p.outputStride p.rows p.cols
  padded : ∀ r, r < p.rows → ∀ a, Footprint (rowAddress p.input p.inputStride r) 8 a →
    m.readable a = true
  separate : ∀ r, r < p.rows → ∀ a, Footprint (rowAddress p.input p.inputStride r) 8 a →
    ¬ p.footprint a

theorem NeonStripSafe.rowSlice {m other : Memory} {p : MatrixCopy}
    (h : NeonStripSafe m p) (start count : Nat) (bound : start+count ≤ p.rows)
    (hr : other.readable = m.readable) (hw : other.writable = m.writable) :
    NeonStripSafe other (p.rowSlice start count) := by
  constructor
  · exact (h.common.rowSlice start count bound).permissions hr hw
  · intro r hh a ha
    change r < count at hh
    change Footprint (rowAddress (p.rowSlice start count).input p.inputStride r) 8 a at ha
    rw [hr]
    exact h.padded (start+r) (by omega) a (by simpa only [rowSlice_input_row] using ha)
  · intro r hh a ha
    have hh : r < count := hh
    change Footprint (rowAddress (p.rowSlice start count).input p.inputStride r) 8 a at ha
    have hf := h.separate (start+r) (by omega) a (by simpa only [rowSlice_input_row] using ha)
    rintro ⟨⟨w,c⟩, ⟨hw,hc⟩, hp⟩
    have hw : w < count := hw
    apply hf ⟨(start+w,c), ⟨by omega,hc⟩, ?_⟩
    simpa only [MatrixCopy.rowSlice_writeAddress] using hp

/-- Writable adjacent row words discharge the actual eight-byte source store. -/
theorem NeonStripSafe.store_pair {m : Memory} {p : MatrixCopy} (h : NeonStripSafe m p)
    (col : Nat) (hc : col < p.cols) (rows : 2 ≤ p.rows) (a : Address)
    (hp : Footprint (p.writeAddress (0,col)) 8 a) : m.writable a = true := by
  have split := (footprint_append (p.writeAddress (0,col)) a 4 4).mp hp
  rcases split with left | right
  · exact h.common.writable 0 (by omega) a (matrix_write_footprint p 0 col hc a left)
  · have he : p.writeAddress (0,col) + BitVec.ofNat 64 4 = p.writeAddress (1,col) := by
      simp [MatrixCopy.writeAddress, BitVec.ofNat_add, BitVec.add_assoc]
    exact h.common.writable 1 (by omega) a (matrix_write_footprint p 1 col hc a (he ▸ right))

/-- A source load can observe the same original padded bytes after any matrix
row prefix has been copied, including its unused odd-column padding. -/
theorem NeonStripSafe.rowSlice_preserves_padding {m : Memory} {p : MatrixCopy}
    (h : NeonStripSafe m p) (start count : Nat) (bound : start+count ≤ p.rows)
    (r : Nat) (hr : r < p.rows) :
    readBytes ((p.rowSlice start count).result m) (rowAddress p.input p.inputStride r) 8 =
      readBytes m (rowAddress p.input p.inputStride r) 8 := by
  apply readBytes_congr
  intro a ha
  apply MatrixCopy.result_frame
  rintro ⟨⟨w,c⟩, ⟨hw,hc⟩, hp⟩
  have hw : w < count := hw
  apply h.separate r hr a ha ⟨(start+w,c), ⟨by omega,hc⟩, ?_⟩
  simpa only [MatrixCopy.rowSlice_writeAddress] using hp

end Salty.Kernels.X32Transpose
