import Salty.Proofs.Rdsum.NeonTailRows

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def batchCountExpr : Expr := .call .floorU64I32
  [.cast .u64 (.bin .div (.cast .u64 (.bin .add (.var "rows") (.cast .u64 (.lit 251)))) (.cast .u64 (.lit 252)))]

theorem floor_count_intrinsic (cfg : Config) (m : Memory) (n : Nat) (bound : n < 2^31) :
    intrinsic cfg m .floorU64I32 [.integer n] = some (.integer n) := by
  have lo : (0 : Int) ≤ n := by omega
  have exactDouble : (n : Int) ≤ 2^53 := by omega
  have intBound : (n : Int) < 2^31 := by omega
  simp only [intrinsic, wideningIntrinsic, lo, exactDouble, intBound, and_self, ↓reduceIte]

/-- The source performs unsigned integer division before its double/floor/int
composition. Under the row-count contract all casts are exact. -/
theorem batch_count_eval (cfg : Config) (s : State) (rows : Nat) (bound : rows < 2^31)
    (hr : s.locals "rows" = some (.integer rows)) :
    eval cfg s batchCountExpr = some (.integer (batchCount rows)) := by
  have sumBound : rows+251 < 2^64 := by omega
  have countBound : batchCount rows < 2^31 := by unfold batchCount; omega
  have add : eval cfg s (.bin .add (.var "rows") (.cast .u64 (.lit 251))) =
      some (.integer (rows+251 : Nat)) := by
    simp [eval, binary, hr, show convert .u64 251 = 251 from rfl, Int.natCast_add]
  have numerator := eval_cast_integer cfg s _ .u64 (rows+251 : Nat) add
  rw [cast_nat _ sumBound] at numerator
  have denominator : eval cfg s (.cast .u64 (.lit 252)) = some (.integer 252) := by
    simp only [eval, show convert .u64 252 = 252 from rfl, pure, bind, Option.bind_some]
  have division : eval cfg s (.bin .div (.cast .u64 (.bin .add (.var "rows") (.cast .u64 (.lit 251))))
      (.cast .u64 (.lit 252))) = some (.integer (batchCount rows)) := by
    rw [eval]
    simp only [numerator, denominator, Option.bind_some, pure, bind, binary]
    rfl
  have argument := eval_cast_integer cfg s _ .u64 (batchCount rows) division
  rw [cast_nat _ (by omega : batchCount rows < 2^64)] at argument
  unfold batchCountExpr
  rw [eval]
  simp only [List.mapM_cons, List.mapM_nil, argument, Option.bind_some, pure, bind,
    floor_count_intrinsic cfg s.memory (batchCount rows) countBound]

theorem neon_batch_count_shape (kind : Interpretation) : firstStatement (neonChannels kind false) =
    .assign "num_batches" batchCountExpr := by cases kind <;> rfl

theorem neon_batch_count_exec (kind : Interpretation) (cfg : Config) (s : State) (rows : Nat)
    (bound : rows < 2^31) (hr : s.locals "rows" = some (.integer rows)) :
    Exec cfg (firstStatement (neonChannels kind false)) s (update s "num_batches" (.integer (batchCount rows))) := by
  rw [neon_batch_count_shape]
  exact .assign (batch_count_eval cfg s rows bound hr)

end Salty.Kernels.Rdsum
