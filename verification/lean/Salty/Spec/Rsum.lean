import Salty.Model.CByteMemory

namespace Salty.Kernels.Rsum
open CByte ReductionISA

/-- The modular 32-bit reduction of the original input bytes. -/
def byteSum (kind : Interpretation) (m : Memory) (input : Address) (n : Nat) : BitVec 32 :=
  sumWords (widen32 kind (readBytes m input n))

/-- C scalar arithmetic after the vector reduction. Signed addition must be
representable; unsigned addition wraps modulo 2^32. -/
def outputScalar (kind : Interpretation) (initial contribution : BitVec 32) : Int :=
  match kind with
  | .signed => initial.toInt + contribution.toInt
  | .unsigned => (BitVec.ofInt 32 ((initial.toNat : Int) + contribution.toNat)).toNat

def OutputDefined (kind : Interpretation) (initial contribution : BitVec 32) : Prop :=
  match kind with
  | .signed => -(2^31) ≤ initial.toInt + contribution.toInt ∧ initial.toInt + contribution.toInt < 2^31
  | .unsigned => True

structure Call where
  count : Nat
  input : Address
  output : Address
  params : Address
  initial : BitVec 32

/-- Common caller contract for the extracted reduction pair.
Inputs include 15 readable padding bytes for the source's last 16-byte load. Both
functions finish all input reads before the sole output store, so input/output
aliasing is permitted. The dummy parameter is never read. Valid live C objects,
the private immutable mask object, and architectural VLEN mapping are supplied
by the trusted bridge; the explicit predicates check addresses and permissions. -/
structure Entry (kind : Interpretation) (s : State) (c : Call) : Prop where
  batch : s.locals "batch" = some (.integer c.count)
  inputPtr : s.locals "input" = some (.pointer c.input)
  outputPtr : s.locals "output" = some (.pointer c.output)
  paramsPtr : s.locals "params" = some (.pointer c.params)
  positive : 0 < c.count
  size : c.count < 2^64
  inputNonzero : c.input ≠ 0
  outputNonzero : c.output ≠ 0
  paramsNonzero : c.params ≠ 0
  inputBound : c.input.toNat + c.count + 15 < 2^64
  outputBound : c.output.toNat + 4 < 2^64
  outputAligned : c.output.toNat % 4 = 0
  readable : ∀ a, Footprint c.input (c.count + 15) a → s.memory.readable a = true
  outputReadable : ∀ a, Footprint c.output 4 a → s.memory.readable a = true
  writable : ∀ a, Footprint c.output 4 a → s.memory.writable a = true
  initialLoad : loadParam s.memory c.output = some (.integer c.initial.toInt)
  defined : OutputDefined kind c.initial (byteSum kind s.memory c.input c.count)

def resultMemory (kind : Interpretation) (m : Memory) (c : Call) : Memory :=
  writeBytes m c.output (bytes32 (outputScalar kind c.initial (byteSum kind m c.input c.count)))

end Salty.Kernels.Rsum
