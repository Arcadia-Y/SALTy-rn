import Salty.Spec.QS8AddLane
import Salty.Spec.BinaryRegions

namespace Salty.Kernels.QS8Add
open CByte QuantizedAddISA
open SIMD.Arithmetic
abbrev Params := QuantizedAddISA.Params

/-- Fixed LP64 caller data; the eight values are bound to the actual packed
24-byte parameter structure by Entry's checked loads. The unused bias is not read. -/
structure Call where
  count : Nat
  inputA : Address
  inputB : Address
  output : Address
  params : Address
  values : Params

/-- Common defined caller domain. Inputs may alias each other, but each padded
input and the parameter object are separate from output. Object lifetimes are
supplied by the C bridge; these predicates check permissions and no wrap.
The raw shift excludes INT32_MIN because the source negates it as signed C.
Observations exclude arithmetic status flags such as FPSR.QC and vxsat. -/
structure Entry (s : State) (c : Call) : Prop where
  batch : s.locals "batch" = some (.integer c.count)
  inputAPtr : s.locals "input_a" = some (.pointer c.inputA)
  inputBPtr : s.locals "input_b" = some (.pointer c.inputB)
  outputPtr : s.locals "output" = some (.pointer c.output)
  paramsPtr : s.locals "params" = some (.pointer c.params)
  positive : 0 < c.count
  size : c.count < 2^64
  inputANonzero : c.inputA ≠ 0
  inputBNonzero : c.inputB ≠ 0
  outputNonzero : c.output ≠ 0
  paramsNonzero : c.params ≠ 0
  inputABound : c.inputA.toNat + c.count + 7 < 2^64
  inputBBound : c.inputB.toNat + c.count + 7 < 2^64
  outputBound : c.output.toNat + c.count < 2^64
  paramsBound : c.params.toNat + 24 < 2^64
  paramsAligned : c.params.toNat % 4 = 0
  memory : BinarySafe s.memory c.inputA c.inputB c.output c.count 7
  paramsReadable : ∀ a, Footprint c.params 24 a → s.memory.readable a = true
  paramsSeparate : ∀ a, Footprint c.params 24 a → ¬ Footprint c.output c.count a
  zeroALoad : s.memory.load c.params = some c.values.aZero
  zeroBLoad : s.memory.load (c.params+1#64) = some c.values.bZero
  multALoad : loadParam s.memory (c.params+8#64) = some (.integer c.values.aMultiplier.toInt)
  multBLoad : loadParam s.memory (c.params+12#64) = some (.integer c.values.bMultiplier.toInt)
  shiftLoad : loadParam s.memory (c.params+16#64) = some (.integer c.values.shift.toInt)
  outputZeroLoad : loadParam16 s.memory (c.params+20#64) = some (.integer c.values.outputZero.toInt)
  outputMinLoad : s.memory.load (c.params+22#64) = some c.values.outputMin
  outputMaxLoad : s.memory.load (c.params+23#64) = some c.values.outputMax
  shiftDefined : c.values.shift.toInt ≠ -(2^31)

/-- Full-memory result from both original input arrays. -/
def resultMemory (s : State) (c : Call) : Memory :=
  binaryResult (neonLane c.values) s.memory c.inputA c.inputB c.output c.count

end Salty.Kernels.QS8Add
