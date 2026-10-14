import Salty.Proofs.Rdsum.NeonShape

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem cast_i32_nat (n : Nat) (bound : n < 2^31) : convert .i32 n = n := by
  change (BitVec.ofNat 32 n).toInt = (n : Int)
  have small : n < 2^32 := by omega
  rw [BitVec.toInt_eq_toNat_of_lt (by simp [Nat.mod_eq_of_lt small]; omega)]
  simp [Nat.mod_eq_of_lt small]

def neonCount (kind : Interpretation) (main : Bool) : Stmt := firstStatement (neonCountLoop kind main)
def neonFinish (kind : Interpretation) (main : Bool) : Stmt :=
  firstStatement (dropStatements (neonChunks kind main+1+neonWidth kind main/4) (neonBatch kind main))

theorem neon_count_shape (kind : Interpretation) (main : Bool) : neonCount kind main =
    .assign (neonCurrent main) (.cast .i32 (.call .minimumU64
      [.cast .u64 (.var (neonRemaining main)), .cast .u64 (.lit 252)])) := by cases main <;> cases kind <;> rfl

theorem neon_finish_shape (kind : Interpretation) (main : Bool) : neonFinish kind main =
    .assign (neonRemaining main) (.cast .i32 (.call .differenceOrZero
      [.cast .u64 (.var (neonRemaining main)), .cast .u64 (.lit 252)])) := by cases main <;> cases kind <;> rfl

theorem minimum_u64_intrinsic (cfg : Config) (m : Memory) (a b : Int)
    (ha : 0 ≤ a ∧ a < 2^64) (hb : 0 ≤ b ∧ b < 2^64) :
    intrinsic cfg m .minimumU64 [.integer a, .integer b] = some (.integer (min a b)) := by
  simp only [intrinsic, wideningIntrinsic, ha.1, ha.2, hb.1, hb.2, and_self, ↓reduceIte]

theorem minimum_batch_intrinsic (cfg : Config) (m : Memory) (remaining : Nat) (bound : remaining < 2^31) :
    intrinsic cfg m .minimumU64 [.integer remaining, .integer 252] = some (.integer (batchSize remaining)) := by
  have mincast : min (remaining : Int) 252 = (batchSize remaining : Nat) := by
    by_cases h : remaining ≤ 252
    · have ih : (remaining : Int) ≤ 252 := by omega
      simp [batchSize, Nat.min_eq_left h, Int.min_eq_left ih]
    · have nh : 252 ≤ remaining := by omega
      have ih : (252 : Int) ≤ remaining := by omega
      simp [batchSize, Nat.min_eq_right nh, Int.min_eq_right ih]
  have call : intrinsic cfg m .minimumU64 [.integer remaining, .integer 252] =
      some (.integer (batchSize remaining)) := by
    rw [minimum_u64_intrinsic cfg m remaining 252 (by omega) (by decide), mincast]

  exact call

theorem eval_cast_integer (cfg : Config) (s : State) (e : Expr) (ty : Scalar) (x : Int)
    (he : eval cfg s e = some (.integer x)) :
    eval cfg s (.cast ty e) = some (.integer (convert ty x)) := by
  rw [eval, he]
  rfl

theorem eval_call_two (cfg : Config) (s : State) (op : Prim) (a b : Expr) (x y result : Value)
    (ha : eval cfg s a = some x) (hb : eval cfg s b = some y)
    (call : intrinsic cfg s.memory op [x,y] = some result) :
    eval cfg s (.call op [a,b]) = some result := by
  rw [eval]
  simp only [List.mapM_cons, List.mapM_nil, ha, hb, pure, bind, Option.bind_some, call]

theorem count_min_exec (cfg : Config) (s : State) (currentName remainingName : String)
    (remaining : Nat) (bound : remaining < 2^31)
    (hr : s.locals remainingName = some (.integer remaining)) :
    Exec cfg (.assign currentName (.cast .i32 (.call .minimumU64
      [.cast .u64 (.var remainingName), .cast .u64 (.lit 252)]))) s (update s currentName (.integer (batchSize remaining))) := by
  have c64 := cast_nat remaining (by omega : remaining < 2^64)
  have c32 := cast_i32_nat (batchSize remaining) (by unfold batchSize; omega)
  have call := minimum_batch_intrinsic cfg s.memory remaining bound
  have arg := eval_cast_integer cfg s (.var remainingName) .u64 remaining (by simpa only [eval] using hr)
  rw [c64] at arg
  have literal := eval_cast_integer cfg s (.lit 252) .u64 252 (by simp only [eval])
  rw [show convert .u64 252 = 252 from rfl] at literal
  have inner := eval_call_two cfg s .minimumU64 (.cast .u64 (.var remainingName)) (.cast .u64 (.lit 252))
    (.integer remaining) (.integer 252) (.integer (batchSize remaining)) arg literal call
  apply Exec.assign
  have outer := eval_cast_integer cfg s _ .i32 (batchSize remaining) inner
  rw [c32] at outer
  exact outer


theorem neon_count_exec (kind : Interpretation) (main : Bool) (cfg : Config) (s : State)
    (remaining : Nat) (bound : remaining < 2^31)
    (hr : s.locals (neonRemaining main) = some (.integer remaining)) :
    Exec cfg (neonCount kind main) s (update s (neonCurrent main) (.integer (batchSize remaining))) := by
  rw [neon_count_shape]
  exact count_min_exec cfg s (neonCurrent main) (neonRemaining main) remaining bound hr

theorem neon_finish_exec (kind : Interpretation) (main : Bool) (cfg : Config) (s : State)
    (remaining : Nat) (bound : remaining < 2^31)
    (hr : s.locals (neonRemaining main) = some (.integer remaining)) :
    Exec cfg (neonFinish kind main) s (update s (neonRemaining main) (.integer (remaining-batchSize remaining : Nat))) := by
  have c64 := cast_nat remaining (by omega : remaining < 2^64)
  have difference : max ((remaining : Int)-252) 0 = (remaining-batchSize remaining : Nat) := by unfold batchSize; omega
  have c32 := cast_i32_nat (remaining-batchSize remaining) (by omega)
  rw [neon_finish_shape]
  apply Exec.assign
  simp [eval, intrinsic, hr, c64, show convert .u64 252 = 252 by decide, difference, c32]

def neonTailReset (kind : Interpretation) : Stmt := firstStatement (neonBatch kind false)

theorem neon_tail_reset_shape (kind : Interpretation) : neonTailReset kind =
    .assign (neonHalfName kind false 0) (.call .dupI16x8
      [.cast (match kind with | .signed => .i16 | .unsigned => .u16) (.lit 0)]) := by cases kind <;> rfl

theorem neon_tail_reset_exec (kind : Interpretation) (cfg : Config) (s : State) :
    Exec cfg (neonTailReset kind) s (update s (neonHalfName kind false 0) (.halfwords (List.replicate 8 0))) := by
  rw [neon_tail_reset_shape]
  apply Exec.assign
  cases kind <;> simp [eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic, convert]

end Salty.Kernels.Rdsum
