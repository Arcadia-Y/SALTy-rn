import Salty.Spec.MatrixLayout

namespace Salty.Kernels.X32Transpose
open CByte

/-- Byte addresses for one row/column displacement, retaining 64-bit wrapping.
A complete C caller contract will separately bound all object addresses. -/
def rowAddress (a : Address) (stride row : Nat) : Address :=
  a + BitVec.ofNat 64 (stride * row)

/-- Original function arguments, before the local width variable is created. -/
structure Arguments (s : State) (p : MatrixCopy) : Prop where
  width : s.locals "block_width" = some (.integer p.cols)
  height : s.locals "block_height" = some (.integer p.rows)
  inputPtr : s.locals "input" = some (.pointer p.input)
  outputPtr : s.locals "output" = some (.pointer p.output)
  inputStride : s.locals "input_stride" = some (.integer p.inputStride)
  outputStride : s.locals "output_stride" = some (.integer p.outputStride)

/-- The source do-loop copies one column at width zero. At height zero neither
program accesses memory. The repaired target explicitly implements these cases. -/
def effectiveMatrix (p : MatrixCopy) : MatrixCopy :=
  {p with cols := if p.rows = 0 then 0 else if p.cols = 0 then 1 else p.cols}

/-- The do-loop always processes at least one source column. At zero height
this still has an empty memory footprint, irrespective of the column count. -/
def sourceMatrix (p : MatrixCopy) : MatrixCopy :=
  {p with cols := if p.cols = 0 then 1 else p.cols}

/-- Live, separate input/output objects for a nonempty transpose. The flat
memory model records permissions; the trusted C bridge interprets these bounded
spans as live objects. Strides need alignment only when used for a second row or
column. Readable source padding includes one word after each input row. -/
structure Storage (m : Memory) (p : MatrixCopy) : Prop where
  inputNonzero : p.input ≠ 0
  outputNonzero : p.output ≠ 0
  inputAligned : p.input.toNat % 4 = 0
  outputAligned : p.output.toNat % 4 = 0
  inputStrideAligned : 1 < p.rows → p.inputStride % 4 = 0
  outputStrideAligned : 1 < p.cols → p.outputStride % 4 = 0
  inputBound : p.input.toNat + (p.rows-1)*p.inputStride + 4*(p.cols+1) < 2^64
  outputBound : p.output.toNat + (p.cols-1)*p.outputStride + 4*p.rows < 2^64
  outputStride : p.cols ≤ 1 ∨ 4*p.rows ≤ p.outputStride
  readable : ∀ r, r < p.rows → ∀ a,
    Footprint (rowAddress p.input p.inputStride r) (4*(p.cols+1)) a → m.readable a = true
  writable : ∀ c, c < p.cols → ∀ a,
    Footprint (p.output + BitVec.ofNat 64 (c*p.outputStride)) (4*p.rows) a → m.writable a = true
  separate : ∀ r, r < p.rows → ∀ a,
    Footprint (rowAddress p.input p.inputStride r) (4*(p.cols+1)) a →
    ∀ c, c < p.cols → ¬ Footprint (p.output + BitVec.ofNat 64 (c*p.outputStride)) (4*p.rows) a

/-- Actual LP64 arguments, source/target assertions with unsigned products,
and a common defined caller domain. Zero-height calls need no live objects,
nonnull pointers, alignment, padding, or unused stride-layout constraints. -/
structure Entry (s : State) (p : MatrixCopy) : Prop where
  arguments : Arguments s p
  rows : p.rows < 2^64
  cols : p.cols < 2^64
  inputStride : p.inputStride < 2^64
  outputStride : p.outputStride < 2^64
  outputAssertion : p.cols = 1 ∨ convert .u64 ((p.rows : Int)*4) ≤ p.outputStride
  inputAssertion : p.rows = 1 ∨ convert .u64 ((p.cols : Int)*4) ≤ p.inputStride
  storage : 0 < p.rows → Storage s.memory (sourceMatrix p)

end Salty.Kernels.X32Transpose
