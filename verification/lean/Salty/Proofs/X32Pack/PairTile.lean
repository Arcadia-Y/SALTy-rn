import Salty.Proofs.X32Pack.TileDefs

namespace Salty.Kernels.X32Pack
open CByte

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

def pairStarted (rvv : Bool) (s : State) (n : Nat) (weights bias output : Address) : State :=
  update (update (pairHeaderAfter rvv s bias output) "w1" (.pointer (weights+BitVec.ofNat 64 (4*n)))) "k" (.integer n)

theorem pair_prefix_exec (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (s : State) (n extra : Nat) (weights bias output : Address)
    (loc : TileLocals s n extra weights bias output) (safe : TileSafe s.memory weights bias output n true) :
    Exec cfg (pairPrefix rvv) s (pairStarted rvv s n weights bias output) := by
  have header := pair_header_exec rvv cfg capacity s bias output ⟨loc.bias,loc.output⟩ safe.header
  have weightLoc : (pairHeaderAfter rvv s bias output).locals "w0" = some (.pointer weights) :=
    (header.locals_frame "w0" (by cases rvv <;> rfl)).trans loc.weights
  have depthLoc : (pairHeaderAfter rvv s bias output).locals "kc" = some (.integer n) :=
    (header.locals_frame "kc" (by cases rvv <;> rfl)).trans loc.depth
  have ptr : BitVec.ofInt 64 (4*(n : Int)) = BitVec.ofNat 64 (4*n) := by
    rw [show 4*(n : Int) = (4*n : Nat) by omega, BitVec.ofInt_natCast]
  rw [pair_prefix_shape]
  refine .seq header (.seq (t := update (pairHeaderAfter rvv s bias output) "w1" (.pointer (weights+BitVec.ofNat 64 (4*n)))) ?_ (.seq ?_ .skip))
  · apply Exec.assign
    simp [eval, weightLoc, depthLoc, ptr]
  · apply Exec.assign
    simp [eval, update_locals, depthLoc]

theorem pairStarted_memory (rvv : Bool) (s : State) (n : Nat) (weights bias output : Address) :
    (pairStarted rvv s n weights bias output).memory = writeBytes s.memory output (headerBytes s.memory bias true) := by
  simp [pairStarted, update_memory, pairHeaderAfter_memory]

theorem pairStarted_locals (rvv : Bool) (s : State) (n extra : Nat) (weights bias output : Address)
    (loc : TileLocals s n extra weights bias output) :
    PairLocals (pairStarted rvv s n weights bias output) n weights
      (weights+BitVec.ofNat 64 (4*n)) (output+8) := by
  constructor <;> by_cases zero : bias = 0#64 <;>
    simp [pairStarted, pairHeaderAfter, zero, update_locals, loc.weights]

def pairFinished (s : State) (weights output : Address) (extra : Nat) : State :=
  update (update s "packed_weights" (.pointer (output+BitVec.ofNat 64 extra))) "w0" (.pointer weights)

theorem pair_suffix_exec (rvv : Bool) (cfg : Config) (s : State) (weights output : Address) (extra : Nat)
    (right : s.locals "w1" = some (.pointer weights))
    (out : s.locals "packed_weights" = some (.pointer output))
    (gap : s.locals "extra_bytes" = some (.integer extra)) :
    Exec cfg (pairSuffix rvv) s (pairFinished s weights output extra) := by
  rw [pair_suffix_shape]
  refine .seq (t := update s "packed_weights" (.pointer (output+BitVec.ofNat 64 extra))) ?_ (.seq ?_ .skip)
  · apply Exec.assign
    simp [eval, binary, out, gap, cast_pointer_add]
  · apply Exec.assign
    simp [eval, update_locals, right]

/-- The complete paired-channel tile body, including bias, both depth paths,
extra bytes and the source's final w0=w1 assignment. -/
theorem pair_tile_total (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (s : State) (n extra : Nat) (weights bias output : Address)
    (loc : TileLocals s n extra weights bias output) (tuple : TupleReady rvv s)
    (bound : 8*n ≤ 2^64) (safe : TileSafe s.memory weights bias output n true) :
    ∃ t, Exec cfg (pairChannelBody rvv) s t ∧ t.memory = writeTile s.memory s.memory weights bias output n true ∧
      TileEnd t (weights+BitVec.ofNat 64 (8*n)) (nextBias bias true)
        (output+BitVec.ofNat 64 (tileSize n extra)) ∧ TupleReady rvv t := by
  let u := pairStarted rvv s n weights bias output
  have front : Exec cfg (pairPrefix rvv) s u := pair_prefix_exec rvv cfg capacity s n extra weights bias output loc safe
  have uLoc := pairStarted_locals rvv s n extra weights bias output loc
  have uMem : u.memory = writeBytes s.memory output (headerBytes s.memory bias true) := pairStarted_memory ..
  have uTuple : TupleReady rvv u := tuple.of_frame (front.locals_frame "v00" (by cases rvv <;> rfl))
  have uSafe : PairSafe u.memory weights (weights+BitVec.ofNat 64 (4*n)) (output+8) n := by
    rw [uMem]; exact safe.after_header
  obtain ⟨v, depth, vMem, vLoc, vTuple⟩ := pair_depth_total rvv cfg u n weights
    (weights+BitVec.ofNat 64 (4*n)) (output+8) uLoc uTuple bound uSafe
  have vExtra : v.locals "extra_bytes" = some (.integer extra) := by
    rw [depth.locals_frame "extra_bytes" (by cases rvv <;> rfl), front.locals_frame "extra_bytes" (by cases rvv <;> rfl)]
    exact loc.extra
  have vBias : v.locals "bias" = some (.pointer (nextBias bias true)) := by
    rw [depth.locals_frame "bias" (by cases rvv <;> rfl)]
    have h := (pairHeaderAfter_locals rvv s bias output ⟨loc.bias,loc.output⟩).bias
    simpa [u, pairStarted, update_locals] using h
  let t := pairFinished v (weights+BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 (4*n))
    (output+8+BitVec.ofNat 64 (8*n)) extra
  have suffix : Exec cfg (pairSuffix rvv) v t := pair_suffix_exec rvv cfg v _ _ extra vLoc.right vLoc.output vExtra
  have outAddress : output+8+BitVec.ofNat 64 (8*n)+BitVec.ofNat 64 extra =
      output+BitVec.ofNat 64 (tileSize n extra) := by
    change output+BitVec.ofNat 64 8+BitVec.ofNat 64 (8*n)+BitVec.ofNat 64 extra = _
    rw [BitVec.add_assoc output, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    simp [tileSize]; omega
  have weightAddress : weights+BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 (4*n) = weights+BitVec.ofNat 64 (8*n) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 4*n+4*n = 8*n by omega]
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · apply exec_take_drop 3 front
    apply exec_take_drop (if rvv then 1 else 2) depth
    cases rvv <;> exact suffix
  · change v.memory = _
    rw [vMem, uMem]
    exact tile_pair_result safe
  · constructor
    · simpa [t, pairFinished, update_locals] using congrArg (fun p => some (Value.pointer p)) weightAddress
    · simp [t, pairFinished, update_locals, vBias]
    · simpa [t, pairFinished, update_locals] using congrArg (fun p => some (Value.pointer p)) outAddress
  · exact vTuple.of_frame (suffix.locals_frame "v00" (by cases rvv <;> rfl))

end Salty.Kernels.X32Pack
