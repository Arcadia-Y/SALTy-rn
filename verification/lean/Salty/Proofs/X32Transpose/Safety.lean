import Salty.Proofs.Core.MatrixSlices
import Salty.Proofs.Core.MatrixRowSlices
import Salty.Proofs.X32Transpose.Execution

namespace Salty.Kernels.X32Transpose
open CByte

theorem DisjointStride32_mono {stride : Address} {small large : Nat}
    (h : DisjointStride32 stride large) (bound : small ≤ large) : DisjointStride32 stride small := by
  rcases h with h | ⟨hs, he⟩
  · exact Or.inl (by omega)
  · right
    exact ⟨hs, Nat.le_trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left stride.toNat (by omega : small - 1 ≤ large - 1)) 4) he⟩

theorem slice_input_footprint (p : MatrixCopy) (start count r : Nat) (address : Address)
    (bound : start + count ≤ p.cols)
    (hp : Footprint (rowAddress (p.slice start count).input p.inputStride r) (4 * count) address) :
    Footprint (rowAddress p.input p.inputStride r) (4 * p.cols) address := by
  apply footprint_shift_within (start := 4 * start) (count := 4 * count) (by omega)
  have he : rowAddress (p.slice start count).input p.inputStride r =
      rowAddress p.input p.inputStride r + BitVec.ofNat 64 (4 * start) := by
    simp only [rowAddress, MatrixCopy.slice]
    ac_rfl
  exact he ▸ hp

theorem slice_output_footprint (p : MatrixCopy) (start count r : Nat) (address : Address)
    (bound : start + count ≤ p.cols)
    (hp : StridedFootprint (rowAddress (p.slice start count).output 4 r)
      (BitVec.ofNat 64 p.outputStride) count address) :
    StridedFootprint (rowAddress p.output 4 r) (BitVec.ofNat 64 p.outputStride) p.cols address := by
  obtain ⟨c, hc, hp⟩ := hp
  refine ⟨start+c, by omega, ?_⟩
  have he : rowAddress (p.slice start count).output 4 r +
      BitVec.ofNat 64 p.outputStride * BitVec.ofNat 64 c =
      rowAddress p.output 4 r + BitVec.ofNat 64 p.outputStride * BitVec.ofNat 64 (start+c) := by
    simp only [rowAddress, MatrixCopy.slice, BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.mul_add]
    ac_rfl
  exact he ▸ hp

theorem RowsSafe.slice {m : Memory} {p : MatrixCopy}
    (h : RowsSafe m p.input p.output p.inputStride p.outputStride p.rows p.cols)
    (start count : Nat) (bound : start + count ≤ p.cols) :
    RowsSafe m (p.slice start count).input (p.slice start count).output
      p.inputStride p.outputStride p.rows count := by
  constructor
  · intro positive
    exact DisjointStride32_mono (h.layout positive) (by omega)
  · intro r hr a ha
    exact h.readable r hr a (slice_input_footprint p start count r a bound ha)
  · intro r hr a ha
    exact h.writable r hr a (slice_output_footprint p start count r a bound ha)
  · intro r hr w hw a ha hb
    exact h.separate r hr w hw a (slice_input_footprint p start count r a bound ha)
      (slice_output_footprint p start count w a bound hb)

theorem RowsSafe.permissions {m other : Memory} {input output : Address}
    {inputStride outputStride rows cols : Nat}
    (h : RowsSafe m input output inputStride outputStride rows cols)
    (hr : other.readable = m.readable) (hw : other.writable = m.writable) :
    RowsSafe other input output inputStride outputStride rows cols := by
  exact ⟨h.layout, by simpa only [hr] using h.readable,
    by simpa only [hw] using h.writable, h.separate⟩

theorem rowSlice_input_row (p : MatrixCopy) (start count r : Nat) :
    rowAddress (p.rowSlice start count).input p.inputStride r =
      rowAddress p.input p.inputStride (start+r) := by
  simp only [rowAddress, MatrixCopy.rowSlice, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_mul]
  ac_rfl

theorem rowSlice_output_row (p : MatrixCopy) (start count r : Nat) :
    rowAddress (p.rowSlice start count).output 4 r = rowAddress p.output 4 (start+r) := by
  simp only [rowAddress, MatrixCopy.rowSlice, Nat.mul_add, BitVec.ofNat_add]
  ac_rfl

theorem RowsSafe.rowSlice {m : Memory} {p : MatrixCopy}
    (h : RowsSafe m p.input p.output p.inputStride p.outputStride p.rows p.cols)
    (start count : Nat) (bound : start+count ≤ p.rows) :
    RowsSafe m (p.rowSlice start count).input (p.rowSlice start count).output
      p.inputStride p.outputStride count p.cols := by
  constructor
  · intro positive
    exact h.layout (by omega)
  · intro r hr a ha
    exact h.readable (start+r) (by omega) a (by simpa only [rowSlice_input_row] using ha)
  · intro r hr a ha
    exact h.writable (start+r) (by omega) a (by simpa only [rowSlice_output_row] using ha)
  · intro r hr w hw a ha hb
    exact h.separate (start+r) (by omega) (start+w) (by omega) a
      (by simpa only [rowSlice_input_row] using ha) (by simpa only [rowSlice_output_row] using hb)

theorem matrix_read_footprint (p : MatrixCopy) (r c : Nat) (hc : c < p.cols)
    (a : Address) (hp : Footprint (p.readAddress (r,c)) 4 a) :
    Footprint (rowAddress p.input p.inputStride r) (4 * p.cols) a := by
  apply footprint_shift_within (start := 4*c) (count := 4) (by omega)
  simpa only [MatrixCopy.readAddress, rowAddress, Nat.mul_comm r p.inputStride,
    BitVec.ofNat_add, BitVec.add_assoc] using hp

theorem matrix_write_footprint (p : MatrixCopy) (r c : Nat) (hc : c < p.cols)
    (a : Address) (hp : Footprint (p.writeAddress (r,c)) 4 a) :
    StridedFootprint (rowAddress p.output 4 r) (BitVec.ofNat 64 p.outputStride) p.cols a := by
  refine ⟨c, hc, ?_⟩
  have he : p.writeAddress (r,c) =
      rowAddress p.output 4 r + BitVec.ofNat 64 p.outputStride * BitVec.ofNat 64 c := by
    simp only [MatrixCopy.writeAddress, rowAddress, BitVec.ofNat_add, BitVec.ofNat_mul]
    ac_rfl
  exact he ▸ hp

/-- Every completed strip preserves every original matrix input word. This is
proved from byte separation, not postulated as an execution result. -/
theorem RowsSafe.slice_preserves_input {m : Memory} {p : MatrixCopy}
    (h : RowsSafe m p.input p.output p.inputStride p.outputStride p.rows p.cols)
    (start count : Nat) (bound : start + count ≤ p.cols) (r c : Nat) (hr : r < p.rows)
    (hc : c < p.cols) :
    readBytes ((p.slice start count).result m) (p.readAddress (r,c)) 4 =
      readBytes m (p.readAddress (r,c)) 4 := by
  apply readBytes_congr
  intro a ha
  apply MatrixCopy.result_frame
  rintro ⟨⟨w,k⟩, ⟨hw,hk⟩, hb⟩
  have hk : k < count := hk
  rw [MatrixCopy.slice_writeAddress] at hb
  exact h.separate r hr w hw a (matrix_read_footprint p r c hc a ha)
    (matrix_write_footprint p w (start+k) (by omega) a hb)

/-- Prefix and remaining strips compose to the same complete matrix copy.
Both strips may choose their own row visitation order internally. -/
theorem RowsSafe.prefix_remaining_result {m : Memory} {p : MatrixCopy}
    (h : RowsSafe m p.input p.output p.inputStride p.outputStride p.rows p.cols)
    (count : Nat) (bound : count ≤ p.cols) (sep : p.separated) :
    (p.slice count (p.cols-count)).result ((p.slice 0 count).result m) = p.result m := by
  rw [p.slice_result m ((p.slice 0 count).result m) count (p.cols-count)
    (by omega) sep (by
      intro r hr c _ hc
      exact h.slice_preserves_input 0 count (by omega) r c hr (by omega))]
  rw [p.slice_result m m 0 count (by omega) sep (by intros; rfl)]
  have split := p.columnFold_add m m 0 count (p.cols-count)
  simp only [Nat.zero_add] at split
  rw [← split]
  rw [Nat.add_sub_of_le bound]
  exact (p.result_columnFold m sep).symm

theorem RowsSafe.rowSlice_preserves_input {m : Memory} {p : MatrixCopy}
    (h : RowsSafe m p.input p.output p.inputStride p.outputStride p.rows p.cols)
    (start count : Nat) (bound : start+count ≤ p.rows) (r c : Nat) (hr : r < p.rows)
    (hc : c < p.cols) :
    readBytes ((p.rowSlice start count).result m) (p.readAddress (r,c)) 4 =
      readBytes m (p.readAddress (r,c)) 4 := by
  apply readBytes_congr
  intro a ha
  apply MatrixCopy.result_frame
  rintro ⟨⟨w,k⟩, ⟨hw,hk⟩, hb⟩
  have hw : w < count := hw
  rw [MatrixCopy.rowSlice_writeAddress] at hb
  exact h.separate r hr (start+w) (by omega) a (matrix_read_footprint p r c hc a ha)
    (matrix_write_footprint p (start+w) k hk a hb)

/-- Fixed-height source tiles and their remaining rows compose using the same
original-input specification as the variable-width target strips. -/
theorem RowsSafe.prefix_remaining_rows_result {m : Memory} {p : MatrixCopy}
    (h : RowsSafe m p.input p.output p.inputStride p.outputStride p.rows p.cols)
    (count : Nat) (bound : count ≤ p.rows) :
    (p.rowSlice count (p.rows-count)).result ((p.rowSlice 0 count).result m) = p.result m := by
  rw [p.rowSlice_result m ((p.rowSlice 0 count).result m) count (p.rows-count) (by
    intro r _ hr c hc
    exact h.rowSlice_preserves_input 0 count (by omega) r c (by omega) hc)]
  rw [p.rowSlice_result m m 0 count (by intros; rfl)]
  have split := p.rowFold_add m m 0 count (p.rows-count)
  simp only [Nat.zero_add] at split
  rw [← split, Nat.add_sub_of_le bound]
  exact (p.result_rowFold m).symm

end Salty.Kernels.X32Transpose
