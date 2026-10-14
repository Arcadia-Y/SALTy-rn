import Salty.Spec.ByteRegions
import Salty.Spec.S8ClampLane

namespace Salty.Kernels.S8Clamp.Execution
open CByte

/-- Caller data at the fixed LP64 ABI. The parameter values are tied to actual
little-endian memory loads by Entry below, rather than supplied as an unrelated
ideal clamp specification. -/
structure Call where
  count : Nat
  input : Address
  output : Address
  params : Address
  min32 : Int
  max32 : Int

def Call.bounds (c : Call) : Params :=
  ⟨BitVec.ofInt 8 c.min32, BitVec.ofInt 8 c.max32⟩

/-- The supported, defined caller domain: nonempty byte arrays, a padded input
object, writable separate output, a readable aligned parameter object, and no
64-bit pointer wrap, including one-past pointers. Parameter/output separation
also discharges the source's restrict obligation for params. The flat byte model
assumes these contiguous regions represent live C objects; allocation/lifetimes
are part of the trusted source bridge, not modeled dynamically. -/
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
  paramsBound : c.params.toNat + 8 < 2^64
  paramsAligned : c.params.toNat % 4 = 0
  memory : PaddedSafe s.memory c.input c.output c.count
  paramsReadable : ∀ a, Footprint c.params 8 a → s.memory.readable a = true
  paramsSeparate : ∀ a, Footprint c.params 8 a → ¬ Footprint c.output c.count a
  minLoad : loadParam s.memory c.params = some (.integer c.min32)
  maxLoad : loadParam s.memory (c.params + 4#64) = some (.integer c.max32)
  ordered : Valid c.bounds

/-- Complete final-memory specification shared by the independently extracted
programs. Only bytes in the output interval may change. -/
def resultMemory (s : State) (c : Call) : Memory :=
  writeBytes s.memory c.output ((readBytes s.memory c.input c.count).map (mainLane c.bounds))

end Salty.Kernels.S8Clamp.Execution
