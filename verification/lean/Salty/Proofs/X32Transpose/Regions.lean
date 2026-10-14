import Salty.Proofs.X32Transpose.NeonColumns

namespace Salty.Kernels.X32Transpose
open CByte

/-- A whole matrix with one readable padding word after each row. The padding
is needed by the source's two-word load on a final one-column strip. -/
structure TransposeSafe (m : Memory) (p : MatrixCopy) : Prop where
  common : RowsSafe m p.input p.output p.inputStride p.outputStride p.rows p.cols
  padded : ∀ r, r < p.rows → ∀ a,
    Footprint (rowAddress p.input p.inputStride r) (4*(p.cols+1)) a → m.readable a = true
  separate : ∀ r, r < p.rows → ∀ a,
    Footprint (rowAddress p.input p.inputStride r) (4*(p.cols+1)) a → ¬ p.footprint a

theorem TransposeSafe.permissions {m other : Memory} {p : MatrixCopy}
    (h : TransposeSafe m p) (hr : other.readable = m.readable) (hw : other.writable = m.writable) :
    TransposeSafe other p := by
  exact ⟨h.common.permissions hr hw, by simpa only [hr] using h.padded, h.separate⟩

theorem TransposeSafe.slice {m : Memory} {p : MatrixCopy} (h : TransposeSafe m p)
    (start count : Nat) (bound : start+count ≤ p.cols) : TransposeSafe m (p.slice start count) := by
  have input (r : Nat) (a : Address)
      (hp : Footprint (rowAddress (p.slice start count).input p.inputStride r) (4*(count+1)) a) :
      Footprint (rowAddress p.input p.inputStride r) (4*(p.cols+1)) a :=
    slice_input_footprint {p with cols := p.cols+1} start (count+1) r a
      (by change start+(count+1) ≤ p.cols+1; omega) hp
  constructor
  · exact h.common.slice start count bound
  · intro r hr a ha
    exact h.padded r hr a (input r a ha)
  · intro r hr a ha
    have hf := h.separate r hr a (input r a ha)
    rintro ⟨⟨w,c⟩, ⟨hw,hc⟩, hp⟩
    have hc : c < count := hc
    apply hf ⟨(w,start+c), ⟨hw,by omega⟩, ?_⟩
    simpa only [MatrixCopy.slice_writeAddress] using hp

theorem TransposeSafe.neon_strip {m : Memory} {p : MatrixCopy} (h : TransposeSafe m p)
    (width : Nat) (bound : (if width < 2 then 1 else 2) ≤ p.cols) :
    NeonStripSafe m (neonActiveStrip p width) := by
  let count := if width < 2 then 1 else 2
  have small : count ≤ p.cols := bound
  have pos : 0 < p.cols := by
    dsimp [count] at small
    split at small <;> omega
  have sliceEq : p.slice 0 count = neonActiveStrip p width := by
    simp [MatrixCopy.slice, neonActiveStrip, count]
  constructor
  · have hc := h.common.slice 0 count (by omega)
    rw [sliceEq] at hc
    exact hc
  · intro r hr a ha
    exact h.padded r hr a (footprint_mono (by omega) ha)
  · intro r hr a ha
    have hf := h.separate r hr a (footprint_mono (by omega) ha)
    rintro ⟨⟨w,c⟩, ⟨hw,hc⟩, hp⟩
    have hc : c < count := hc
    exact hf ⟨(w,c), ⟨hw,by omega⟩, hp⟩

end Salty.Kernels.X32Transpose
