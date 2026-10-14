import Salty.Model.CWordMemory

namespace Salty.CByte

structure MatrixCopy where
  input : Address
  output : Address
  inputStride : Nat
  outputStride : Nat
  rows : Nat
  cols : Nat

def MatrixCopy.readAddress (p : MatrixCopy) (rc : Nat × Nat) : Address :=
  p.input + BitVec.ofNat 64 (rc.1 * p.inputStride + 4 * rc.2)

def MatrixCopy.writeAddress (p : MatrixCopy) (rc : Nat × Nat) : Address :=
  p.output + BitVec.ofNat 64 (rc.2 * p.outputStride + 4 * rc.1)

def MatrixCopy.valid (p : MatrixCopy) (rc : Nat × Nat) : Prop :=
  rc.1 < p.rows ∧ rc.2 < p.cols

/-- Pairwise byte-disjoint destinations; a concrete caller contract should
derive this from dimensions, strides and address bounds. -/
def MatrixCopy.separated (p : MatrixCopy) : Prop :=
  ∀ a b, p.valid a → p.valid b → a ≠ b → ∀ address,
    Footprint (p.writeAddress a) 4 address → ¬ Footprint (p.writeAddress b) 4 address

/-- Read the original input memory, write one transposed word. This definition
makes the copy result independent of prior writes; source refinement must prove
that its reads indeed observe these original bytes. -/
def MatrixCopy.writeWord (p : MatrixCopy) (original working : Memory) (rc : Nat × Nat) : Memory :=
  writeBytes working (p.writeAddress rc) (readBytes original (p.readAddress rc) 4)

def MatrixCopy.rowVisits (p : MatrixCopy) : List (Nat × Nat) :=
  (List.range p.rows).flatMap (fun r => (List.range p.cols).map (fun c => (r,c)))

def MatrixCopy.columnVisits (p : MatrixCopy) : List (Nat × Nat) :=
  (List.range p.cols).flatMap (fun c => (List.range p.rows).map (fun r => (r,c)))

def MatrixCopy.result (p : MatrixCopy) (original : Memory) : Memory :=
  p.rowVisits.foldl (p.writeWord original) original

/-- Sufficient standard output geometry. Nonwrapping live-object bounds and
alignment are additional C caller obligations, not inferred from this predicate. -/
structure MatrixCopy.DestinationLayout (p : MatrixCopy) : Prop where
  stride : p.cols ≤ 1 ∨ 4 * p.rows ≤ p.outputStride
  extent : (p.cols - 1) * p.outputStride + 4 * p.rows ≤ 2^64

def MatrixCopy.footprint (p : MatrixCopy) (address : Address) : Prop :=
  ∃ rc, p.valid rc ∧ Footprint (p.writeAddress rc) 4 address

def MatrixCopy.writeRow (p : MatrixCopy) (original working : Memory) (row : Nat) : Memory :=
  (List.range p.cols).foldl (fun mem col => p.writeWord original mem (row,col)) working

end Salty.CByte
