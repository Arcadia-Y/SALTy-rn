import Salty.Spec.S8ClampLane
import Salty.Proofs.Core.ByteISA
import Salty.Proofs.Core.Stripmine

/-! A stream-level refinement target for s8-vclamp. This module independently
models the source's 64/8/tail schedule and the target's VL-driven schedule.
It does not yet connect those models to C or ByteISA executions, and therefore
is not included in the concrete kernel coverage count. -/
namespace Salty.Kernels.S8Clamp
open ByteISA

theorem clamp_order (p : Params) (valid : Valid p) (x : Byte) :
    tailLane p x = mainLane p x := by
  unfold tailLane mainLane minSigned maxSigned
  unfold Valid at valid
  repeat' split
  all_goals first | rfl | (apply BitVec.eq_of_toInt_eq; omega)

def neon (p : Params) (input : List Byte) : List Byte :=
  if input.length ≥ 64 then
    (input.take 64).map (mainLane p) ++ neon p (input.drop 64)
  else if input.length ≥ 8 then
    (input.take 8).map (tailLane p) ++ neon p (input.drop 8)
  else input.map (tailLane p)
termination_by input.length

def rvv (p : Params) (schedule : Schedule) (input : List Byte) : List Byte :=
  stripmine schedule (mainLane p) input

theorem neon_eq_map (p : Params) (valid : Valid p) (input : List Byte) :
    neon p input = input.map (mainLane p) := by
  rw [neon]
  split
  · rw [neon_eq_map p valid (input.drop 64), ← List.map_append, List.take_append_drop]
  · split
    · have lane : tailLane p = mainLane p := funext (clamp_order p valid)
      rw [lane, neon_eq_map p valid (input.drop 8), ← List.map_append, List.take_append_drop]
    · exact List.map_congr_left (fun _ _ => clamp_order p valid _)
termination_by input.length

theorem stream_equivalent (p : Params) (valid : Valid p) (schedule : Schedule) (input : List Byte) :
    neon p input = rvv p schedule input := by
  rw [neon_eq_map p valid, rvv, stripmine_eq_map]

end Salty.Kernels.S8Clamp
