import Salty.Proofs.X32Pack.PairTile

namespace Salty.Kernels.X32Pack
open CByte

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

def oddChannelBody (rvv : Bool) : Stmt := if rvv then rvvOdd else neonOdd
def oddPrefix (rvv : Bool) : Stmt := takeStatements 3 (oddChannelBody rvv)
def oddDepth (rvv : Bool) : Stmt := firstStatement (dropStatements 3 (oddChannelBody rvv))
def oddSuffix (rvv : Bool) : Stmt := dropStatements 4 (oddChannelBody rvv)

def oddStarted (s : State) (n : Nat) (bias output : Address) : State :=
  update (oddHeaderAfter s bias output) "k_2" (.integer n)

theorem odd_prefix_exec (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (s : State) (n extra : Nat) (weights bias output : Address)
    (loc : TileLocals s n extra weights bias output) (safe : TileSafe s.memory weights bias output n false) :
    Exec cfg (oddPrefix rvv) s (oddStarted s n bias output) := by
  have header := odd_header_exec rvv cfg capacity s bias output ⟨loc.bias,loc.output⟩ safe.header
  have depthLoc : (oddHeaderAfter s bias output).locals "kc" = some (.integer n) :=
    (header.locals_frame "kc" (by cases rvv <;> rfl)).trans loc.depth
  apply exec_take_drop (code := oddPrefix rvv) 2
  · cases rvv <;> exact header
  have assign : Exec cfg (.seq (.assign "k_2" (.var "kc")) .skip)
      (oddHeaderAfter s bias output) (oddStarted s n bias output) := by
    refine .seq ?_ .skip
    apply Exec.assign
    simp [eval, depthLoc]
  cases rvv <;> exact assign

theorem oddStarted_memory (s : State) (n : Nat) (bias output : Address) :
    (oddStarted s n bias output).memory = writeBytes s.memory output (headerBytes s.memory bias false) := by
  simp [oddStarted, update_memory, oddHeaderAfter_memory]

theorem oddStarted_locals (s : State) (n extra : Nat) (weights bias output : Address)
    (loc : TileLocals s n extra weights bias output) :
    SingleLocals (oddStarted s n bias output) n weights (output+8) := by
  constructor <;> by_cases zero : bias = 0#64 <;>
    simp [oddStarted, oddHeaderAfter, oddHeaderWritten, zero, update_locals, loc.weights]

theorem odd_depth_total (rvv : Bool) (cfg : Config) (s : State) (n : Nat) (weights output : Address)
    (loc : SingleLocals s n weights output) (positive : 0 < n)
    (bound : 8*n ≤ 2^64) (safe : PairSafe s.memory weights weights output n) :
    ∃ t, Exec cfg (oddDepth rvv) s t ∧ t.memory = singleResult s.memory weights output n ∧
      SingleLocals t 0 (weights+BitVec.ofNat 64 (4*n)) (output+BitVec.ofNat 64 (8*n)) := by
  cases rvv with
  | true => exact rvv_single_loop_total cfg s n weights output loc bound safe
  | false => exact neon_single_depth_total cfg s n weights output loc positive bound safe

theorem odd_suffix_shape (rvv : Bool) : oddSuffix rvv =
    .seq (.assign "packed_weights" (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var "packed_weights")) (.var "extra_bytes"))))) .skip := by
  cases rvv <;> rfl

theorem odd_suffix_exec (rvv : Bool) (cfg : Config) (s : State) (output : Address) (extra : Nat)
    (out : s.locals "packed_weights" = some (.pointer output))
    (gap : s.locals "extra_bytes" = some (.integer extra)) :
    Exec cfg (oddSuffix rvv) s (update s "packed_weights" (.pointer (output+BitVec.ofNat 64 extra))) := by
  rw [odd_suffix_shape]
  refine .seq ?_ .skip
  apply Exec.assign
  simp [eval, binary, out, gap, cast_pointer_add]

/-- Complete odd-channel body. Its second header word is preserved precisely
when bias is present; the second word of every weight pair is always preserved. -/
theorem odd_tile_total (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (s : State) (n extra : Nat) (weights bias output : Address)
    (loc : TileLocals s n extra weights bias output) (tuple : TupleReady rvv s)
    (positive : 0 < n) (bound : 8*n ≤ 2^64) (safe : TileSafe s.memory weights bias output n false) :
    ∃ t, Exec cfg (oddChannelBody rvv) s t ∧ t.memory = writeTile s.memory s.memory weights bias output n false ∧
      TileEnd t (weights+BitVec.ofNat 64 (4*n)) (nextBias bias false)
        (output+BitVec.ofNat 64 (tileSize n extra)) ∧ TupleReady rvv t := by
  let u := oddStarted s n bias output
  have front : Exec cfg (oddPrefix rvv) s u := odd_prefix_exec rvv cfg capacity s n extra weights bias output loc safe
  have uLoc := oddStarted_locals s n extra weights bias output loc
  have uMem : u.memory = writeBytes s.memory output (headerBytes s.memory bias false) := oddStarted_memory ..
  have uSafe : PairSafe u.memory weights weights (output+8) n := by rw [uMem]; exact safe.after_header
  obtain ⟨v, depth, vMem, vLoc⟩ := odd_depth_total rvv cfg u n weights (output+8) uLoc positive bound uSafe
  have vExtra : v.locals "extra_bytes" = some (.integer extra) := by
    rw [depth.locals_frame "extra_bytes" (by cases rvv <;> rfl), front.locals_frame "extra_bytes" (by cases rvv <;> rfl)]
    exact loc.extra
  have vBias : v.locals "bias" = some (.pointer (nextBias bias false)) := by
    rw [depth.locals_frame "bias" (by cases rvv <;> rfl)]
    have h := (oddHeaderAfter_locals s bias output ⟨loc.bias,loc.output⟩).bias
    simpa [u, oddStarted, update_locals] using h
  let t := update v "packed_weights" (.pointer (output+8+BitVec.ofNat 64 (8*n)+BitVec.ofNat 64 extra))
  have suffix : Exec cfg (oddSuffix rvv) v t := odd_suffix_exec rvv cfg v _ extra vLoc.output vExtra
  have complete : Exec cfg (oddChannelBody rvv) s t := by
    apply exec_take_drop 3 front
    have rest : Exec cfg (.seq (oddDepth rvv) (oddSuffix rvv)) u t := .seq depth suffix
    cases rvv <;> exact rest
  have outAddress : output+8+BitVec.ofNat 64 (8*n)+BitVec.ofNat 64 extra =
      output+BitVec.ofNat 64 (tileSize n extra) := by
    change output+BitVec.ofNat 64 8+BitVec.ofNat 64 (8*n)+BitVec.ofNat 64 extra = _
    rw [BitVec.add_assoc output, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    simp [tileSize]; omega
  refine ⟨t, complete, ?_, ?_, tuple.of_frame (complete.locals_frame "v00" (by cases rvv <;> rfl))⟩
  · change v.memory = _
    rw [vMem, uMem]
    exact tile_single_result safe
  · constructor
    · simpa [t, update_locals] using vLoc.input
    · simp [t, update_locals, vBias]
    · simpa [t, update_locals] using congrArg (fun p => some (Value.pointer p)) outAddress

end Salty.Kernels.X32Pack
