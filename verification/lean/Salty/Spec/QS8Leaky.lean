import Salty.Spec.QS8LeakyLane
import Salty.Spec.ByteRegions

namespace Salty.Kernels.QS8Leaky
open CByte
open S8Clamp.Execution (PaddedSafe)
abbrev neonLane := QuantizedLeakyISA.neonLane
abbrev rvvLane := QuantizedLeakyISA.rvvLane

abbrev Params := QuantizedLeakyISA.Params

/-- Fixed LP64 caller data. All four parameters are tied to actual memory
loads by Entry, including the 32-bit multipliers negated before narrowing. -/
structure Call where
  count : Nat
  input : Address
  output : Address
  params : Address
  inputZero : BitVec 32
  positive : BitVec 32
  negative : BitVec 32
  outputZero : BitVec 32

def Call.values (c : Call) : Params :=
  ⟨BitVec.ofInt 16 c.inputZero.toInt, BitVec.ofInt 16 (-c.positive.toInt),
    BitVec.ofInt 16 (-c.negative.toInt), BitVec.ofInt 16 c.outputZero.toInt⟩

/-- Common defined caller domain: live padded input, separate writable output,
live readable aligned parameters disjoint from output (restrict), and no pointer
wrap. Allocation/lifetime validity is supplied by the trusted C bridge. Signed
negation of INT32_MIN is undefined C and therefore excluded explicitly.
The ABI-call observation excludes FPSR.QC/vxsat and other status flags. -/
structure Entry (s : State) (c : Call) : Prop where
  batch : s.locals "batch" = some (.integer c.count)
  inputPtr : s.locals "input" = some (.pointer c.input)
  outputPtr : s.locals "output" = some (.pointer c.output)
  paramsPtr : s.locals "params" = some (.pointer c.params)
  positive : 0 < c.count
  size : c.count < 2^64
  inputNonzero : c.input ≠ 0
  outputNonzero : c.output ≠ 0
  paramsNonzero : c.params ≠ 0
  inputBound : c.input.toNat + c.count + 7 < 2^64
  outputBound : c.output.toNat + c.count < 2^64
  paramsBound : c.params.toNat + 16 < 2^64
  paramsAligned : c.params.toNat % 4 = 0
  memory : PaddedSafe s.memory c.input c.output c.count
  paramsReadable : ∀ a, Footprint c.params 16 a → s.memory.readable a = true
  paramsSeparate : ∀ a, Footprint c.params 16 a → ¬ Footprint c.output c.count a
  inputZeroLoad : loadParam s.memory c.params = some (.integer c.inputZero.toInt)
  positiveLoad : loadParam s.memory (c.params + 4#64) = some (.integer c.positive.toInt)
  negativeLoad : loadParam s.memory (c.params + 8#64) = some (.integer c.negative.toInt)
  outputZeroLoad : loadParam s.memory (c.params + 12#64) = some (.integer c.outputZero.toInt)
  positiveDefined : c.positive.toInt ≠ -(2^31)
  negativeDefined : c.negative.toInt ≠ -(2^31)

/-- Full-memory result, including preservation of every non-output byte. -/
def resultMemory (s : State) (c : Call) : Memory :=
  writeBytes s.memory c.output ((readBytes s.memory c.input c.count).map (neonLane c.values))

end Salty.Kernels.QS8Leaky
