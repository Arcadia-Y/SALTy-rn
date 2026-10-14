import Salty.Proofs.X32Transpose.Correct

namespace Salty.Kernels.X32Transpose
open CByte

/-- A nonempty admitted call: one word at 16 with source padding, one output
word at 64, and explicit aligned byte strides. -/
def witnessMatrix : MatrixCopy := ⟨16#64,64#64,8,4,1,1⟩

def stateFor (p : MatrixCopy) : State :=
  ⟨fun name =>
    if name = "block_width" then some (.integer p.cols)
    else if name = "block_height" then some (.integer p.rows)
    else if name = "input_stride" then some (.integer p.inputStride)
    else if name = "output_stride" then some (.integer p.outputStride)
    else if name = "input" then some (.pointer p.input)
    else if name = "output" then some (.pointer p.output)
    else none,
    ⟨fun _ => 0, fun _ => true, fun _ => true⟩⟩

def witnessState : State := stateFor witnessMatrix

theorem stateFor_arguments (p : MatrixCopy) : Arguments (stateFor p) p := by
  constructor <;> simp [stateFor]

private theorem witness_disjoint (a : Address) (left : Footprint (16#64) 8 a)
    (right : Footprint (64#64) 4 a) : False := by
  obtain ⟨i, hi, he⟩ := left
  obtain ⟨j, hj, hf⟩ := right
  have hn := congrArg BitVec.toNat (he.symm.trans hf)
  simp [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
  omega

theorem entry_nonempty : Entry witnessState witnessMatrix := by
  constructor
  · exact stateFor_arguments witnessMatrix
  · decide
  · decide
  · decide
  · decide
  · exact Or.inl rfl
  · exact Or.inl rfl
  · intro positive
    constructor
    all_goals try decide
    · intro r hr a ha; rfl
    · intro c hc a ha; rfl
    · intro r hr a ha c hc hb
      have rzero : r = 0 := by change r < 1 at hr; omega
      have czero : c = 0 := by change c < 1 at hc; omega
      subst r
      subst c
      apply witness_disjoint a
      · simpa [sourceMatrix, witnessMatrix, rowAddress] using ha
      · simpa [sourceMatrix, witnessMatrix] using hb

/-- Empty-height calls may use null pointers and very large size_t widths and
strides. Unsigned assertion products still determine whether the call is valid. -/
def emptyMatrix : MatrixCopy := ⟨0,0,2^64-4,2^64-1,0,2^64-1⟩

theorem entry_empty_large : Entry (stateFor emptyMatrix) emptyMatrix := by
  constructor
  · exact stateFor_arguments emptyMatrix
  · decide
  · decide
  · decide
  · decide
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)
  · intro positive
    change 0 < 0 at positive
    omega

end Salty.Kernels.X32Transpose
