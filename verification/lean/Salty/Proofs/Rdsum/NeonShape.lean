import Salty.Proofs.Rdsum.RvvCorrect
import Salty.Generated.QS8RdsumNeon
import Salty.Generated.QU8RdsumNeon

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

def neonProgram : Interpretation → Stmt
  | .signed => Generated.QS8Rdsum.neon
  | .unsigned => Generated.QU8Rdsum.neon

def branchYes : Stmt → Stmt
  | .branch _ yes _ => yes
  | _ => .skip

def neonWidth (kind : Interpretation) (main : Bool) : Nat :=
  if main then match kind with | .signed => 16 | .unsigned => 32 else 8

def neonChunks (kind : Interpretation) (main : Bool) : Nat := neonWidth kind main / 8

def neonChannels (kind : Interpretation) (main : Bool) : Stmt :=
  if main then firstStatement (loopBody (firstStatement (dropStatements 5 (neonProgram kind))))
  else firstStatement (firstStatement (dropStatements
    (match kind with | .signed => 1 | .unsigned => 2)
    (branchYes (firstStatement (dropStatements 6 (neonProgram kind))))))

def neonRowLoop (kind : Interpretation) (main : Bool) : Stmt :=
  firstStatement (dropStatements (if main then 8+neonWidth kind main/4 else 11) (neonChannels kind main))

def neonBatch (kind : Interpretation) (main : Bool) : Stmt :=
  if main then loopBody (neonRowLoop kind main) else firstStatement (loopBody (neonRowLoop kind main))

def neonCountLoop (kind : Interpretation) (main : Bool) : Stmt :=
  firstStatement (dropStatements (neonChunks kind main) (neonBatch kind main))

def neonInnerLoop (kind : Interpretation) (main : Bool) : Stmt := dropStatements 1 (neonCountLoop kind main)
def neonGroup (kind : Interpretation) (main : Bool) : Stmt := firstStatement (loopBody (neonInnerLoop kind main))

def neonRowName (main : Bool) (i : Nat) : String :=
  if main then rowName i else match i with
  | 0 => "i0_2" | 1 => "i1_2" | 2 => "i2_2" | 3 => "i3_2"
  | 4 => "i4_2" | 5 => "i5_2" | 6 => "i6_2" | _ => "invalid-row"

def neonCurrent (main : Bool) : String := if main then "current_batch" else "current_batch_2"
def neonRemaining (main : Bool) : String := if main then "r" else "r_2"

def neonHalfName (kind : Interpretation) (main : Bool) (chunk : Nat) : String :=
  if main then match kind, chunk with
    | .signed, 0 => "vacc16_0" | .signed, _ => "vacc16_8"
    | .unsigned, 0 => "vacc16_4" | .unsigned, 1 => "vacc16_12"
    | .unsigned, 2 => "vacc16_20" | .unsigned, _ => "vacc16_28"
  else match kind with | .signed => "vacc16" | .unsigned => "vacc16_2"

def neonWordName (main : Bool) (chunk : Nat) : String :=
  if main then match chunk with
    | 0 => "vacc0" | 1 => "vacc4" | 2 => "vacc8" | 3 => "vacc12"
    | 4 => "vacc16" | 5 => "vacc20" | 6 => "vacc24" | _ => "vacc28"
  else if chunk = 0 then "vacc0_2" else "vacc1"

theorem neon_inner_shape (kind : Interpretation) (main : Bool) : neonInnerLoop kind main =
    .loop (.bin .gt (.var (neonCurrent main)) (.lit 0))
      (.seq (neonGroup kind main) (.assign (neonCurrent main)
        (.checkedSigned32 (.bin .sub (.var (neonCurrent main)) (.lit 7))))) := by
  cases main <;> cases kind <;> rfl

end Salty.Kernels.Rdsum
