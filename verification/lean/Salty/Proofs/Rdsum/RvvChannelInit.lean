import Salty.Proofs.Rdsum.RvvRows

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def rvvChannelInit (kind : Interpretation) : Stmt := takeStatements 10 (rvvChannels kind)

def rowsInitialized (s : State) (input : Address) (stride : Nat) : State :=
  let s := update s "i0" (.pointer input)
  let s := update s "i1" (.pointer (input+BitVec.ofNat 64 (1*stride)))
  let s := update s "i2" (.pointer (input+BitVec.ofNat 64 (2*stride)))
  let s := update s "i3" (.pointer (input+BitVec.ofNat 64 (3*stride)))
  let s := update s "i4" (.pointer (input+BitVec.ofNat 64 (4*stride)))
  let s := update s "i5" (.pointer (input+BitVec.ofNat 64 (5*stride)))
  update s "i6" (.pointer (input+BitVec.ofNat 64 (6*stride)))

def channelInitialized (kind : Interpretation) (s : State) (input : Address)
    (stride rows width : Nat) : State :=
  let s := update s "vl" (.integer width)
  match kind with
  | .signed =>
    let s := rowsInitialized s input stride
    let s := update s "vacc" (.words32 (List.replicate width 0))
    update s "r" (.integer rows)
  | .unsigned =>
    let s := update s "vacc32" (.words32 (List.replicate width 0))
    let s := update s "r" (.integer rows)
    rowsInitialized s input stride

private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

private theorem cast_word (n : Int) : BitVec.ofInt 64 (convert .u64 n) = BitVec.ofInt 64 n := by
  change BitVec.ofInt 64 ((BitVec.ofInt 64 n).toNat : Int) = BitVec.ofInt 64 n
  simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem cast_rows (rows : Nat) (bound : rows < 2^31) : convert .i32 rows = rows := by
  change (BitVec.ofNat 32 rows).toInt = (rows : Int)
  have small : rows < 2^32 := by omega
  rw [BitVec.toInt_eq_toNat_of_lt (by simp [Nat.mod_eq_of_lt small]; omega)]
  simp [Nat.mod_eq_of_lt small]

theorem rvv_channel_init_exec (kind : Interpretation) (cfg : Config) (s : State)
    (input : Address) (stride rows channels : Nat) (bound : rows < 2^31)
    (hl : s.locals "channels" = some (.integer channels))
    (hi : s.locals "input" = some (.pointer input))
    (hs : s.locals "input_stride" = some (.integer stride))
    (hr : s.locals "rows" = some (.integer rows)) :
    Exec cfg (rvvChannelInit kind) s (channelInitialized kind s input stride rows (cfg.choose channels)) := by
  have cap : cfg.choose channels ≤ cfg.capacity := Nat.le_trans (cfg.bounded channels) (Nat.min_le_right ..)
  have cr := cast_rows rows bound
  apply run_sound (fuel := 14)
  cases kind <;>
    simp [rvvChannelInit, rvvChannels, rvvProgram, Generated.QS8Rdsum.rvv, Generated.QU8Rdsum.rvv,
      takeStatements, dropStatements, firstStatement, loopBody, run, eval, binary,
      intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
      channelInitialized, rowsInitialized, update_locals, hl, hi, hs, hr, cap, cr, cast_word, BitVec.ofInt_add, BitVec.ofInt_mul,
      BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofNat_mul,
      show convert .u32 0 = 0 by decide,
      show convert .u64 1 = 1 by decide, show convert .u64 2 = 2 by decide,
      show convert .u64 3 = 3 by decide, show convert .u64 4 = 4 by decide,
      show convert .u64 5 = 5 by decide, show convert .u64 6 = 6 by decide]

@[simp] theorem channelInitialized_memory (kind : Interpretation) (s : State) (input : Address)
    (stride rows width : Nat) : (channelInitialized kind s input stride rows width).memory = s.memory := by
  cases kind <;> rfl

theorem channelInitialized_locals (kind : Interpretation) (s : State) (input zero : Address)
    (stride rows width : Nat)
    (hz : s.locals "zero" = some (.pointer zero))
    (hs : s.locals "input_increment" = some (.integer (7*stride))) :
    BatchLocals kind (channelInitialized kind s input stride rows width)
      (fun i => input+BitVec.ofNat 64 (i*stride)) zero rows width stride (fun _ => 0) := by
  cases kind <;> constructor
  all_goals try { simp [channelInitialized, rowsInitialized, update_locals, accumulatorName, hz, hs, List.map_const'] }
  all_goals
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [channelInitialized, rowsInitialized, update_locals, rowName]

end Salty.Kernels.Rdsum
