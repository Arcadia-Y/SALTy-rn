import Salty.Proofs.Rdsum.OutputMemory

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

structure ChannelLocals (s : State) (rows channels stride : Nat) (input zero output : Address) : Prop where
  rows : s.locals "rows" = some (.integer rows)
  channels : s.locals "channels" = some (.integer channels)
  strideLocal : s.locals "input_stride" = some (.integer stride)
  input : s.locals "input" = some (.pointer input)
  zero : s.locals "zero" = some (.pointer zero)
  output : s.locals "output" = some (.pointer output)
  increment : s.locals "input_increment" = some (.integer (7*stride))

def rvvAdvance (kind : Interpretation) : Stmt := dropStatements 14 (rvvChannels kind)

def channelAdvanced (kind : Interpretation) (s : State) (input output : Address) (channels width : Nat) : State :=
  match kind with
  | .signed =>
    let s := update s "channels" (.integer (channels-width : Nat))
    let s := update s "input" (.pointer (input+BitVec.ofNat 64 width))
    update s "output" (.pointer (output+BitVec.ofNat 64 (4*width)))
  | .unsigned =>
    let s := update s "input" (.pointer (input+BitVec.ofNat 64 width))
    let s := update s "output" (.pointer (output+BitVec.ofNat 64 (4*width)))
    update s "channels" (.integer (channels-width : Nat))

private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

theorem rvv_advance_exec (kind : Interpretation) (cfg : Config) (s : State) (input output : Address)
    (channels width : Nat) (bound : channels < 2^64) (within : width ≤ channels)
    (hi : s.locals "input" = some (.pointer input))
    (ho : s.locals "output" = some (.pointer output))
    (hc : s.locals "channels" = some (.integer channels))
    (hv : s.locals "vl" = some (.integer width)) :
    Exec cfg (rvvAdvance kind) s (channelAdvanced kind s input output channels width) := by
  have sub := cast_sub channels width within bound
  have offset : BitVec.ofInt 64 (4*(width : Int)) = BitVec.ofNat 64 (4*width) := by
    rw [BitVec.ofInt_mul, BitVec.ofNat_mul]
    rfl
  cases kind <;> apply run_sound (fuel := 5) <;>
    simp [rvvAdvance, rvvChannels, rvvProgram, Generated.QS8Rdsum.rvv, Generated.QU8Rdsum.rvv,
      dropStatements, firstStatement, loopBody, run, eval, binary, channelAdvanced,
      update_locals, hi, ho, hc, hv, sub, offset, BitVec.ofInt_natCast]

@[simp] theorem channelAdvanced_memory (kind : Interpretation) (s : State) (input output : Address)
    (channels width : Nat) : (channelAdvanced kind s input output channels width).memory = s.memory := by
  cases kind <;> rfl

theorem channelAdvanced_locals (kind : Interpretation) (s : State) (rows channels stride width : Nat)
    (input zero output : Address) (loc : ChannelLocals s rows channels stride input zero output) :
    ChannelLocals (channelAdvanced kind s input output channels width) rows (channels-width) stride
      (input+BitVec.ofNat 64 width) zero (output+BitVec.ofNat 64 (4*width)) := by
  cases kind <;> constructor <;>
    simp [channelAdvanced, update_locals, loc.rows, loc.strideLocal, loc.zero, loc.increment]

end Salty.Kernels.Rdsum
