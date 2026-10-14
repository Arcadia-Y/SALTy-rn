import Salty.Proofs.Rdsum.NeonBatchCount

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def neonTailInit (kind : Interpretation) : Stmt := takeStatements 11 (neonChannels kind false)
def neonTailInitRest (kind : Interpretation) : Stmt := takeStatements 10 (dropStatements 1 (neonChannels kind false))

def neonTailInitRestCode (kind : Interpretation) : Stmt :=
  (.seq (.assign "r_2" (.cast .i32 (.var "rows")))
  (.seq (.assign "i0_2" (.var "input"))
  (.seq (.assign "i1_2" (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var "input")) (.cast .u64 (.bin .mul (.cast .u64 (.lit 1)) (.var "input_stride")))))))
  (.seq (.assign "i2_2" (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var "input")) (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.var "input_stride")))))))
  (.seq (.assign "i3_2" (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var "input")) (.cast .u64 (.bin .mul (.cast .u64 (.lit 3)) (.var "input_stride")))))))
  (.seq (.assign "i4_2" (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var "input")) (.cast .u64 (.bin .mul (.cast .u64 (.lit 4)) (.var "input_stride")))))))
  (.seq (.assign "i5_2" (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var "input")) (.cast .u64 (.bin .mul (.cast .u64 (.lit 5)) (.var "input_stride")))))))
  (.seq (.assign "i6_2" (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var "input")) (.cast .u64 (.bin .mul (.cast .u64 (.lit 6)) (.var "input_stride")))))))
  (.seq (.assign "vacc0_2" (.call .dupI32x4 [match kind with | .signed => .lit 0 | .unsigned => .cast .u32 (.lit 0)]))
  (.seq (.assign "vacc1" (.call .dupI32x4 [match kind with | .signed => .lit 0 | .unsigned => .cast .u32 (.lit 0)]))
  .skip))))))))))

theorem neon_tail_init_rest_shape (kind : Interpretation) : neonTailInitRest kind = neonTailInitRestCode kind := by
  cases kind <;> rfl

def neonTailRestAfter (s : State) (input : Address) (stride rows : Nat) : State :=
  let s := update s "r_2" (.integer rows)
  let s := update s "i0_2" (.pointer (input+BitVec.ofNat 64 (0*stride)))
  let s := update s "i1_2" (.pointer (input+BitVec.ofNat 64 (1*stride)))
  let s := update s "i2_2" (.pointer (input+BitVec.ofNat 64 (2*stride)))
  let s := update s "i3_2" (.pointer (input+BitVec.ofNat 64 (3*stride)))
  let s := update s "i4_2" (.pointer (input+BitVec.ofNat 64 (4*stride)))
  let s := update s "i5_2" (.pointer (input+BitVec.ofNat 64 (5*stride)))
  let s := update s "i6_2" (.pointer (input+BitVec.ofNat 64 (6*stride)))
  let s := update s "vacc0_2" (.words32 (List.replicate 4 0))
  update s "vacc1" (.words32 (List.replicate 4 0))

def neonTailInitialized (s : State) (input : Address) (stride rows : Nat) : State :=
  neonTailRestAfter (update s "num_batches" (.integer (batchCount rows))) input stride rows

private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

private theorem cast_word (n : Int) : BitVec.ofInt 64 (convert .u64 n) = BitVec.ofInt 64 n := by
  change BitVec.ofInt 64 ((BitVec.ofInt 64 n).toNat : Int) = BitVec.ofInt 64 n
  simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem neon_tail_init_rest_exec (kind : Interpretation) (cfg : Config) (s : State) (input : Address)
    (stride rows : Nat) (bound : rows < 2^31)
    (hi : s.locals "input" = some (.pointer input))
    (hs : s.locals "input_stride" = some (.integer stride))
    (hr : s.locals "rows" = some (.integer rows)) :
    Exec cfg (neonTailInitRest kind) s (neonTailRestAfter s input stride rows) := by
  rw [neon_tail_init_rest_shape]
  cases kind <;> apply run_sound (fuel := 13) <;>
    simp [neonTailInitRestCode, neonTailRestAfter, run, eval, binary, intrinsic, saturatingIntrinsic,
      selectionIntrinsic, integerArithmeticIntrinsic, update_locals, hi, hs, hr, cast_i32_nat rows bound,
      cast_word, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.ofNat_mul, show convert .u32 0 = 0 from rfl,
      show convert .u64 1 = 1 from rfl, show convert .u64 2 = 2 from rfl,
      show convert .u64 3 = 3 from rfl, show convert .u64 4 = 4 from rfl,
      show convert .u64 5 = 5 from rfl, show convert .u64 6 = 6 from rfl]

theorem neon_tail_init_exec (kind : Interpretation) (cfg : Config) (s : State) (input : Address)
    (stride rows : Nat) (bound : rows < 2^31)
    (hi : s.locals "input" = some (.pointer input))
    (hs : s.locals "input_stride" = some (.integer stride))
    (hr : s.locals "rows" = some (.integer rows)) :
    Exec cfg (neonTailInit kind) s (neonTailInitialized s input stride rows) := by
  have count := neon_batch_count_exec kind cfg s rows bound hr
  apply exec_take_drop (t := update s "num_batches" (.integer (batchCount rows))) 1
  · have shape : takeStatements 1 (neonTailInit kind) = .seq (firstStatement (neonChannels kind false)) .skip := by cases kind <;> rfl
    rw [shape]; exact .seq count .skip
  · have shape : dropStatements 1 (neonTailInit kind) = neonTailInitRest kind := by cases kind <;> rfl
    rw [shape]
    exact neon_tail_init_rest_exec kind cfg _ input stride rows bound
      (by simpa [update_locals] using hi) (by simpa [update_locals] using hs) (by simpa [update_locals] using hr)

@[simp] theorem neonTailInitialized_memory (s : State) (input : Address) (stride rows : Nat) :
    (neonTailInitialized s input stride rows).memory = s.memory := rfl

theorem neonTailInitialized_num (s : State) (input : Address) (stride rows : Nat) :
    (neonTailInitialized s input stride rows).locals "num_batches" = some (.integer (batchCount rows)) := by
  simp [neonTailInitialized, neonTailRestAfter, update_locals]

theorem neonTailInitialized_locals (s : State) (input zero : Address) (stride rows : Nat)
    (hz : s.locals "zero" = some (.pointer zero))
    (hs : s.locals "input_increment" = some (.integer (7*stride))) :
    NeonTailBatchLocals (neonTailInitialized s input stride rows)
      (fun i => input+BitVec.ofNat 64 (i*stride)) zero rows stride (fun _ => 0) := by
  constructor
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [neonTailInitialized, neonTailRestAfter, update_locals, neonRowName]
  all_goals simp [neonTailInitialized, neonTailRestAfter, update_locals, hz, hs, List.map_const']

end Salty.Kernels.Rdsum
