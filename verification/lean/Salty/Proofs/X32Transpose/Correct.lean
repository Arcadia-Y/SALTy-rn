import Salty.Spec.X32Transpose
import Salty.Proofs.X32Transpose.Neon
import Salty.Proofs.Core.CByteMachine

namespace Salty.Kernels.X32Transpose
open CByte

theorem word_in_output_column (p : MatrixCopy) (r c : Nat) (hr : r < p.rows)
    (a : Address) (hp : Footprint (p.writeAddress (r,c)) 4 a) :
    Footprint (p.output + BitVec.ofNat 64 (c*p.outputStride)) (4*p.rows) a := by
  apply footprint_shift_within (start := 4*r) (count := 4) (by omega)
  simpa only [MatrixCopy.writeAddress, BitVec.ofNat_add, BitVec.add_assoc] using hp

theorem strided_in_output_column (p : MatrixCopy) (r : Nat) (hr : r < p.rows)
    (a : Address) (hp : StridedFootprint (rowAddress p.output 4 r)
      (BitVec.ofNat 64 p.outputStride) p.cols a) :
    ∃ c, c < p.cols ∧ Footprint (p.output + BitVec.ofNat 64 (c*p.outputStride)) (4*p.rows) a := by
  obtain ⟨c, hc, hp⟩ := hp
  refine ⟨c, hc, word_in_output_column p r c hr a ?_⟩
  have he : rowAddress p.output 4 r + BitVec.ofNat 64 p.outputStride * BitVec.ofNat 64 c =
      p.writeAddress (r,c) := by
    simp only [rowAddress, MatrixCopy.writeAddress, BitVec.ofNat_add, BitVec.ofNat_mul]
    ac_rfl
  exact he ▸ hp

theorem Storage.safe {m : Memory} {p : MatrixCopy} (h : Storage m p)
    (strideBound : p.outputStride < 2^64) : TransposeSafe m p := by
  constructor
  · constructor
    · intro positive
      rcases h.outputStride with small | stride
      · exact Or.inl small
      · right
        have hv : (BitVec.ofNat 64 p.outputStride).toNat = p.outputStride := by
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt strideBound]
        rw [hv]
        have hb := h.outputBound
        constructor
        · omega
        · rw [Nat.mul_comm p.outputStride (p.cols-1)]
          omega
    · intro r hr a ha
      exact h.readable r hr a (footprint_mono (by omega) ha)
    · intro r hr a ha
      obtain ⟨c, hc, hp⟩ := strided_in_output_column p r hr a ha
      exact h.writable c hc a hp
    · intro r hr w hw a ha hb
      obtain ⟨c, hc, hp⟩ := strided_in_output_column p w hw a hb
      exact h.separate r hr a (footprint_mono (by omega) ha) c hc hp
  · exact h.readable
  · intro r hr a ha
    rintro ⟨⟨w,c⟩, ⟨hw,hc⟩, hp⟩
    exact h.separate r hr a ha c hc (word_in_output_column p w c hw a hp)

theorem Storage.separated {m : Memory} {p : MatrixCopy} (h : Storage m p) : p.separated := by
  apply MatrixCopy.DestinationLayout.separated
  exact ⟨h.outputStride, by have := h.outputBound; omega⟩

theorem transpose_safe_empty (m : Memory) (p : MatrixCopy) (empty : p.rows = 0) : TransposeSafe m p := by
  constructor
  · constructor
    · intro positive; omega
    · intro r hr; omega
    · intro r hr; omega
    · intro r hr; omega
  · intro r hr; omega
  · intro r hr; omega

theorem matrix_separated_empty (p : MatrixCopy) (empty : p.rows = 0) : p.separated := by
  intro a b ha
  have := ha.1
  omega

theorem Entry.source_safe {s : State} {p : MatrixCopy} (h : Entry s p) :
    TransposeSafe s.memory (sourceMatrix p) := by
  by_cases empty : p.rows = 0
  · exact transpose_safe_empty s.memory (sourceMatrix p) empty
  · exact (h.storage (by omega)).safe h.outputStride

theorem Entry.source_separated {s : State} {p : MatrixCopy} (h : Entry s p) : (sourceMatrix p).separated := by
  by_cases empty : p.rows = 0
  · exact matrix_separated_empty (sourceMatrix p) empty
  · exact (h.storage (by omega)).separated

theorem Entry.effective_safe {s : State} {p : MatrixCopy} (h : Entry s p) :
    TransposeSafe s.memory (effectiveMatrix p) := by
  by_cases empty : p.rows = 0
  · exact transpose_safe_empty s.memory (effectiveMatrix p) empty
  · simpa only [sourceMatrix, effectiveMatrix, empty, ↓reduceIte] using h.source_safe

theorem Entry.effective_separated {s : State} {p : MatrixCopy} (h : Entry s p) : (effectiveMatrix p).separated := by
  by_cases empty : p.rows = 0
  · exact matrix_separated_empty (effectiveMatrix p) empty
  · simpa only [sourceMatrix, effectiveMatrix, empty, ↓reduceIte] using h.source_separated

/-- Both whole generated programs terminate and return the same complete
memory. The premises concern actual ABI arguments and byte-access domains. -/
theorem extracted_equivalent (cfg : Config) (p : MatrixCopy) :
    CByte.Equivalent cfg Generated.X32Transpose.neon Generated.X32Transpose.rvv (fun s => Entry s p) := by
  intro s h
  obtain ⟨a, ha, hma⟩ := neon_function_total cfg s p h.arguments h.rows h.outputAssertion h.inputAssertion
    h.source_safe h.source_separated
  obtain ⟨b, hb, hmb⟩ := rvv_function_total cfg s p h.arguments h.rows h.cols h.outputAssertion h.inputAssertion
    h.effective_safe.common h.effective_separated
  exact ⟨a,b,ha,hb,hma.trans hmb.symm⟩

/-- The same return/fault/divergence relation used throughout the suite. Every
progressing bounded VL schedule is quantified, and all memory is observed. -/
theorem behavior_equivalent_proof (cfg : Config) (p : MatrixCopy) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.X32Transpose.neon],s⟩)
      (fun s => ⟨[Generated.X32Transpose.rvv],s⟩) (fun s => Entry s p) :=
  (extracted_equivalent cfg p).behavior

theorem result_frame (s : State) (p : MatrixCopy) (a : Address)
    (outside : ¬ (effectiveMatrix p).footprint a) :
    ((effectiveMatrix p).result s.memory).data a = s.memory.data a :=
  (effectiveMatrix p).result_frame s.memory a outside

end Salty.Kernels.X32Transpose
