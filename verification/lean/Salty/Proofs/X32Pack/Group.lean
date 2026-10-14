import Salty.Proofs.X32Pack.GroupMemory

namespace Salty.Kernels.X32Pack
open CByte

structure GroupLocals (s : State) (channels depth extra : Nat) (weights bias output : Address) : Prop where
  channels : s.locals "nc" = some (.integer channels)
  depth : s.locals "kc" = some (.integer depth)
  extra : s.locals "extra_bytes" = some (.integer extra)
  weights : s.locals "weights" = some (.pointer weights)
  bias : s.locals "bias" = some (.pointer bias)
  output : s.locals "packed_weights" = some (.pointer output)

def groupProgram (rvv : Bool) : Stmt := if rvv then rvvGroup else neonGroup

def groupStarted (s : State) (channels : Nat) (weights : Address) : State :=
  update (update s "w0" (.pointer weights)) "n" (.integer channels)

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

theorem group_prefix_shape (rvv : Bool) : takeStatements 2 (groupProgram rvv) =
    .seq (.assign "w0" (.var "weights")) (.seq (.assign "n" (.var "nc")) .skip) := by cases rvv <;> rfl

theorem group_suffix_shape (rvv : Bool) : dropStatements 4 (groupProgram rvv) =
    .seq (.assign "weights" (.offset 4 (.var "weights") (.cast .u64 (.bin .mul (.var "nc") (.var "kc"))))) .skip := by
  cases rvv <;> rfl

theorem group_prefix_exec (rvv : Bool) (cfg : Config) (s : State) (channels depth extra : Nat)
    (weights bias output : Address) (loc : GroupLocals s channels depth extra weights bias output) :
    Exec cfg (takeStatements 2 (groupProgram rvv)) s (groupStarted s channels weights) := by
  rw [group_prefix_shape]
  refine .seq (t := update s "w0" (.pointer weights)) ?_ (.seq ?_ .skip)
  · apply Exec.assign; simpa [eval] using loc.weights
  · apply Exec.assign; simp [eval, update_locals, loc.channels]

theorem group_suffix_exec (rvv : Bool) (cfg : Config) (s : State) (channels depth : Nat) (weights : Address)
    (nc : s.locals "nc" = some (.integer channels)) (kc : s.locals "kc" = some (.integer depth))
    (input : s.locals "weights" = some (.pointer weights)) (bound : channels*depth < 2^64) :
    Exec cfg (dropStatements 4 (groupProgram rvv)) s
      (update s "weights" (.pointer (weights+BitVec.ofNat 64 (weightBytes channels depth)))) := by
  have product : convert .u64 ((channels : Int)*depth) = (channels*depth : Nat) := by
    rw [← Int.natCast_mul]
    exact cast_nat _ bound
  have ptr : BitVec.ofInt 64 (4*((channels*depth : Nat) : Int)) = BitVec.ofNat 64 (weightBytes channels depth) := by
    rw [show 4*((channels*depth : Nat) : Int) = (4*(channels*depth) : Nat) by omega, BitVec.ofInt_natCast]
    congr 1
    unfold weightBytes
    ac_rfl
  rw [group_suffix_shape]
  refine .seq ?_ .skip
  apply Exec.assign
  simp only [eval, nc, kc, input, binary, Option.bind_some, pure, bind, product]
  change some (Value.pointer (weights+BitVec.ofInt 64 (4*((channels*depth : Nat) : Int)))) = _
  rw [ptr]

/-- One complete actual group body, including its local channel reset and
post-channel weights += nc*kc update. -/
theorem group_total (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (channels depth extra : Nat) (s : State) (weights bias output : Address)
    (loc : GroupLocals s channels depth extra weights bias output) (tuple : TupleReady rvv s)
    (size : channels < 2^64) (positive : 0 < depth) (depthBound : 8*depth ≤ 2^64)
    (productBound : channels*depth < 2^64)
    (safe : ChannelSafe s.memory weights bias output channels depth extra) :
    ∃ t, Exec cfg (groupProgram rvv) s t ∧
      t.memory = (packChannels s.memory weights bias output channels depth extra).memory ∧
      GroupLocals t channels depth extra (weights+BitVec.ofNat 64 (weightBytes channels depth))
        (biasAdvance bias channels) (output+BitVec.ofNat 64 (groupBytes channels depth extra)) ∧ TupleReady rvv t := by
  let u := groupStarted s channels weights
  have front : Exec cfg (takeStatements 2 (groupProgram rvv)) s u := group_prefix_exec rvv cfg s channels depth extra weights bias output loc
  have uMem : u.memory = s.memory := rfl
  have uCount : u.locals "n" = some (.integer channels) := by simp [u, groupStarted, update_locals]
  have uLoc : TileLocals u depth extra weights bias output := by
    constructor <;> simp [u, groupStarted, update_locals, loc.depth, loc.extra, loc.bias, loc.output]
  have uTuple : TupleReady rvv u := tuple.of_frame (front.locals_frame "v00" (by cases rvv <;> rfl))
  obtain ⟨v, channelsExec, vMem, vEnd, vTuple⟩ := channels_total rvv cfg capacity channels depth extra u weights bias output
    uCount uLoc uTuple size positive depthBound safe
  have vNc : v.locals "nc" = some (.integer channels) := by
    rw [channelsExec.locals_frame "nc" (by cases rvv <;> rfl), front.locals_frame "nc" (by cases rvv <;> rfl)]
    exact loc.channels
  have vKc : v.locals "kc" = some (.integer depth) := by
    rw [channelsExec.locals_frame "kc" (by cases rvv <;> rfl), front.locals_frame "kc" (by cases rvv <;> rfl)]
    exact loc.depth
  have vExtra : v.locals "extra_bytes" = some (.integer extra) := by
    rw [channelsExec.locals_frame "extra_bytes" (by cases rvv <;> rfl), front.locals_frame "extra_bytes" (by cases rvv <;> rfl)]
    exact loc.extra
  have vWeights : v.locals "weights" = some (.pointer weights) := by
    rw [channelsExec.locals_frame "weights" (by cases rvv <;> rfl), front.locals_frame "weights" (by cases rvv <;> rfl)]
    exact loc.weights
  let t := update v "weights" (.pointer (weights+BitVec.ofNat 64 (weightBytes channels depth)))
  have suffix : Exec cfg (dropStatements 4 (groupProgram rvv)) v t := group_suffix_exec rvv cfg v channels depth weights vNc vKc vWeights productBound
  refine ⟨t, ?_, ?_, ?_, vTuple.of_frame (suffix.locals_frame "v00" (by cases rvv <;> rfl))⟩
  · apply exec_take_drop 2 front
    apply exec_take_drop 2 channelsExec
    cases rvv <;> exact suffix
  · simpa only [uMem] using vMem
  · constructor
    · simpa [t, update_locals] using vNc
    · simpa [t, update_locals] using vKc
    · simpa [t, update_locals] using vExtra
    · simp [t, update_locals]
    · have h := vEnd.bias
      rw [packChannels_bias _ _ _ _ _ _ _ safe.biasBound] at h
      simpa [t, update_locals] using h
    · have h := vEnd.output
      rw [packChannels_output] at h
      simpa [t, update_locals, groupBytes] using h

end Salty.Kernels.X32Pack
