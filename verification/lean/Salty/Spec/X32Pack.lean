import Salty.Model.CWordMemory

namespace Salty.Kernels.X32Pack
open CByte

structure Call where
  groups : Nat
  channels : Nat
  depth : Nat
  weights : Address
  bias : Address
  output : Address
  extra : Nat
  scale : Address
  params : Address

def tiles (channels : Nat) : Nat := (channels+1)/2

def tileSize (depth extra : Nat) : Nat := 8*(depth+1)+extra

def outputSize (c : Call) : Nat := c.groups * tiles c.channels * tileSize c.depth c.extra

/-- Explicit caller contract for the packing development. Bias is optional;
scale and params are unused. Extra bytes and odd-channel weight holes retain
their original contents, as does the unused header word when bias is present.
Without bias, both header words are zeroed even in an odd final tile. The allocation,
lifetime and fixed LP64/little-endian interpretation are trusted bridge duties.
`Salty.Results.X32Pack` connects this contract to both complete functions. -/
structure Entry (s : State) (c : Call) : Prop where
  groups : s.locals "g" = some (.integer c.groups)
  channels : s.locals "nc" = some (.integer c.channels)
  depth : s.locals "kc" = some (.integer c.depth)
  nr : s.locals "nr" = some (.integer 2)
  kr : s.locals "kr" = some (.integer 1)
  sr : s.locals "sr" = some (.integer 1)
  weights : s.locals "weights" = some (.pointer c.weights)
  bias : s.locals "bias" = some (.pointer c.bias)
  output : s.locals "packed_weights" = some (.pointer c.output)
  extra : s.locals "extra_bytes" = some (.integer c.extra)
  scale : s.locals "scale" = some (.pointer c.scale)
  params : s.locals "params" = some (.pointer c.params)
  groupsPositive : 0 < c.groups
  channelsPositive : 0 < c.channels
  depthPositive : 0 < c.depth
  groupsSize : c.groups < 2^64
  channelsSize : c.channels < 2^64
  depthSize : c.depth < 2^64
  extraSize : c.extra < 2^64
  weightsNonzero : c.weights ≠ 0
  outputNonzero : c.output ≠ 0
  weightsAligned : c.weights.toNat % 4 = 0
  biasAligned : c.bias.toNat % 4 = 0
  outputAligned : c.output.toNat % 4 = 0
  extraAligned : c.extra % 4 = 0
  weightsBound : c.weights.toNat + 4*c.groups*c.channels*c.depth < 2^64
  biasBound : c.bias ≠ 0 → c.bias.toNat + 4*c.groups*c.channels < 2^64
  outputBound : c.output.toNat + outputSize c < 2^64
  weightsReadable : ∀ a, Footprint c.weights (4*c.groups*c.channels*c.depth) a → s.memory.readable a = true
  biasReadable : c.bias ≠ 0 → ∀ a, Footprint c.bias (4*c.groups*c.channels) a → s.memory.readable a = true
  outputWritable : ∀ a, Footprint c.output (outputSize c) a → s.memory.writable a = true
  weightsSeparate : ∀ a, Footprint c.weights (4*c.groups*c.channels*c.depth) a → ¬ Footprint c.output (outputSize c) a
  biasSeparate : c.bias ≠ 0 → ∀ a, Footprint c.bias (4*c.groups*c.channels) a → ¬ Footprint c.output (outputSize c) a

/-- Packed two-channel tile. All values come from the original input memory.
A missing bias zeroes both header words, including an odd final tile. -/
def writeTile (original destination : Memory) (weights bias output : Address)
    (depth : Nat) (paired : Bool) : Memory :=
  let header := if bias = 0 then List.replicate 8 0
    else readBytes original bias (if paired then 8 else 4)
  let withHeader := writeBytes destination output header
  if paired then
    writeBytes withHeader (output+8)
      (interleaveWords (readBytes original weights (4*depth))
        (readBytes original (weights+BitVec.ofNat 64 (4*depth)) (4*depth)) depth)
  else
    writeStrided32 withHeader (output+8) 8 (readBytes original weights (4*depth)) depth
def nextBias (bias : Address) (paired : Bool) : Address :=
  if bias = 0 then 0 else bias + (if paired then 8 else 4)

structure ChannelResult where
  memory : Memory
  weights : Address
  bias : Address
  output : Address

/-- Reference fold over complete two-channel tiles, independent of vector
width and instruction schedule. The remaining odd channel is handled separately. -/
def packPairs (depth extra : Nat) : Nat → Memory → Address → Address → Address → ChannelResult
  | 0, m, weights, bias, output => ⟨m,weights,bias,output⟩
  | pairs+1, m, weights, bias, output =>
    packPairs depth extra pairs (writeTile m m weights bias output depth true)
      (weights+BitVec.ofNat 64 (8*depth)) (nextBias bias true)
      (output+BitVec.ofNat 64 (tileSize depth extra))

def oddResult (r : ChannelResult) (depth extra : Nat) : ChannelResult :=
  ⟨writeTile r.memory r.memory r.weights r.bias r.output depth false,
    r.weights+BitVec.ofNat 64 (4*depth), nextBias r.bias false,
    r.output+BitVec.ofNat 64 (tileSize depth extra)⟩

def packChannels (m : Memory) (weights bias output : Address) (channels depth extra : Nat) : ChannelResult :=
  let paired := packPairs depth extra (channels/2) m weights bias output
  if channels%2 = 0 then paired else oddResult paired depth extra

def biasAdvance (bias : Address) (channels : Nat) : Address :=
  if bias = 0 then 0 else bias+BitVec.ofNat 64 (4*channels)

def groupBytes (channels depth extra : Nat) : Nat := tiles channels*tileSize depth extra

def weightBytes (channels depth : Nat) : Nat := 4*depth*channels

/-- Group-major scalar reference traversal. Within each group, packChannels
specifies bias headers, interleaved words, odd holes and extra-byte gaps. -/
def packGroups (channels depth extra : Nat) : Nat → Memory → Address → Address → Address → Memory
  | 0, m, _, _, _ => m
  | groups+1, m, weights, bias, output =>
    packGroups channels depth extra groups (packChannels m weights bias output channels depth extra).memory
      (weights+BitVec.ofNat 64 (weightBytes channels depth)) (biasAdvance bias channels)
      (output+BitVec.ofNat 64 (groupBytes channels depth extra))

end Salty.Kernels.X32Pack
