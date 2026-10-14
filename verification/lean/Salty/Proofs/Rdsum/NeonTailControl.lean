import Salty.Proofs.Rdsum.NeonScalarStore
import Salty.Proofs.Rdsum.NeonAdvance8
import Salty.Proofs.Rdsum.WordPrefix

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def tailBitMask (index : Nat) : Nat := if index = 0 then 4 else if index = 1 then 2 else 1

def tailBitExpr (mask : Nat) : Expr :=
  .cast .u64 (.bin .band (.var "channels") (.cast .u64 (.lit mask)))

def neonTailBranch (kind : Interpretation) (index : Nat) : Stmt :=
  firstStatement (dropStatements index (branchNo (neonTailOutput kind)))

theorem neon_tail_branch_shape (kind : Interpretation) (index : Nat) (within : index < 3) :
    neonTailBranch kind index = .branch (tailBitExpr (tailBitMask index))
      (branchYes (neonTailBranch kind index)) .skip := by
  have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases cases with rfl | rfl | rfl <;> cases kind <;> rfl

theorem tail_bit_eval (cfg : Config) (s : State) (channels mask : Nat)
    (cb : channels < 2^64) (mb : mask < 2^64)
    (hc : s.locals "channels" = some (.integer channels)) :
    eval cfg s (tailBitExpr mask) = some (.integer (channels &&& mask)) := by
  have inside : eval cfg s (.bin .band (.var "channels") (.cast .u64 (.lit mask))) =
      some (.integer (channels &&& mask)) := by
    simp [eval, binary, hc, cast_nat mask mb]
  have result := eval_cast_integer cfg s _ .u64 _ inside
  rw [cast_nat _ (Nat.lt_of_le_of_lt Nat.and_le_left cb)] at result
  exact result

theorem tail_branch_yes (kind : Interpretation) (cfg : Config) (s t : State) (channels index : Nat)
    (cb : channels < 2^64) (within : index < 3)
    (hc : s.locals "channels" = some (.integer channels))
    (bit : channels &&& tailBitMask index ≠ 0)
    (body : Exec cfg (branchYes (neonTailBranch kind index)) s t) :
    Exec cfg (neonTailBranch kind index) s t := by
  rw [neon_tail_branch_shape kind index within]
  apply Exec.yes (tail_bit_eval cfg s channels (tailBitMask index) cb (by by_cases h0 : index = 0 <;> by_cases h1 : index = 1 <;> simp [tailBitMask, h0, h1]) hc) ?_ body
  simp [truth, bit]

theorem tail_branch_no (kind : Interpretation) (cfg : Config) (s : State) (channels index : Nat)
    (cb : channels < 2^64) (within : index < 3)
    (hc : s.locals "channels" = some (.integer channels))
    (bit : channels &&& tailBitMask index = 0) :
    Exec cfg (neonTailBranch kind index) s s := by
  rw [neon_tail_branch_shape kind index within]
  apply Exec.no (tail_bit_eval cfg s channels (tailBitMask index) cb (by by_cases h0 : index = 0 <;> by_cases h1 : index = 1 <;> simp [tailBitMask, h0, h1]) hc) ?_ .skip
  simp [truth, bit]

def neonTailClear (kind : Interpretation) : Stmt :=
  dropStatements 3 (branchNo (neonTailOutput kind))

theorem neon_tail_clear_exec (kind : Interpretation) (cfg : Config) (s : State) :
    Exec cfg (neonTailClear kind) s (update s "channels" (.integer 0)) := by
  have shape : neonTailClear kind = .seq (.assign "channels" (.cast .u64 (.lit 0))) .skip := by
    cases kind <;> rfl
  rw [shape]
  exact .seq (.assign (by simp [eval, show convert .u64 0 = 0 from rfl])) .skip

end Salty.Kernels.Rdsum
