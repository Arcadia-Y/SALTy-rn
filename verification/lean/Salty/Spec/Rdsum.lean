import Salty.Model.CWordCodec

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

structure Call where
  rows : Nat
  channels : Nat
  input : Address
  stride : Nat
  zero : Address
  output : Address
  params : Address

/-- Original input bytes down one column, in increasing row order. -/
def columnBytes (m : Memory) (input : Address) (stride rows column : Nat) : List Byte :=
  (List.range rows).map (fun row => m.data (input + BitVec.ofNat 64 (row*stride+column)))

def columnSum (kind : Interpretation) (m : Memory) (input : Address)
    (stride rows column : Nat) : BitVec 32 :=
  sumWords (widen32 kind (columnBytes m input stride rows column))

def outputWord (kind : Interpretation) (m : Memory) (c : Call) (column : Nat) : BitVec 32 :=
  readWord32 m (c.output+BitVec.ofNat 64 (4*column)) +
    columnSum kind m c.input c.stride c.rows column

def outputWords (kind : Interpretation) (m : Memory) (c : Call) : List (BitVec 32) :=
  (List.range c.channels).map (outputWord kind m c)

def resultMemory (kind : Interpretation) (m : Memory) (c : Call) : Memory :=
  writeBytes m c.output (encodeWords32 (outputWords kind m c))

/-- Only the final odd scalar store uses checked C signed addition. All vector
adds, and the unsigned scalar store, have modular 32-bit behavior. -/
def ScalarTailDefined (kind : Interpretation) (m : Memory) (c : Call) : Prop :=
  match kind with
  | .unsigned => True
  | .signed => c.channels % 2 = 1 →
      let initial := readWord32 m (c.output+BitVec.ofNat 64 (4*(c.channels-1)));
      let contribution := columnSum kind m c.input c.stride c.rows (c.channels-1);
      -(2^31) ≤ initial.toInt+contribution.toInt ∧ initial.toInt+contribution.toInt < 2^31

/-- Common caller domain for the signed and unsigned row-sum theorems. Source `int r`
requires a representable positive row count. Each row has fifteen readable tail
bytes; the zero buffer covers the largest source load or active RVV prefix.
Output is separate from all input/padding and zero bytes. Input rows may overlap.
Live C object provenance, alignment of typed output objects and the architecture's
VLEN mapping remain part of the named extraction/ABI bridge. Params is unused. -/
structure Entry (kind : Interpretation) (s : State) (c : Call) : Prop where
  rowsLocal : s.locals "rows" = some (.integer c.rows)
  channelsLocal : s.locals "channels" = some (.integer c.channels)
  inputLocal : s.locals "input" = some (.pointer c.input)
  strideLocal : s.locals "input_stride" = some (.integer c.stride)
  zeroLocal : s.locals "zero" = some (.pointer c.zero)
  outputLocal : s.locals "output" = some (.pointer c.output)
  paramsLocal : s.locals "params" = some (.pointer c.params)
  rowsPositive : 0 < c.rows
  rowsInt : c.rows < 2^31
  channelsPositive : 0 < c.channels
  channelsSize : c.channels < 2^64
  strideSize : 7*c.stride < 2^64
  inputNonzero : c.input ≠ 0
  outputNonzero : c.output ≠ 0
  zeroNonzero : c.zero ≠ 0
  inputBound : c.input.toNat+(c.rows-1)*c.stride+c.channels+15 < 2^64
  zeroBound : c.zero.toNat+max c.channels 40 < 2^64
  outputBound : c.output.toNat+4*c.channels < 2^64
  outputAligned : c.output.toNat % 4 = 0
  inputReadable : ∀ row, row < c.rows → ∀ a,
    Footprint (c.input+BitVec.ofNat 64 (row*c.stride)) (c.channels+15) a → s.memory.readable a = true
  zeroReadable : ∀ a, Footprint c.zero (max c.channels 40) a → s.memory.readable a = true
  zeroContents : ∀ a, Footprint c.zero (max c.channels 40) a → s.memory.data a = 0
  outputReadable : ∀ a, Footprint c.output (4*c.channels) a → s.memory.readable a = true
  outputWritable : ∀ a, Footprint c.output (4*c.channels) a → s.memory.writable a = true
  inputSeparate : ∀ row, row < c.rows → ∀ a,
    Footprint (c.input+BitVec.ofNat 64 (row*c.stride)) (c.channels+15) a →
      ¬ Footprint c.output (4*c.channels) a
  zeroSeparate : ∀ a, Footprint c.zero (max c.channels 40) a → ¬ Footprint c.output (4*c.channels) a
  scalarDefined : ScalarTailDefined kind s.memory c

end Salty.Kernels.Rdsum
