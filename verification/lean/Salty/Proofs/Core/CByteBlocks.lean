import Salty.Proofs.Core.CByteSyntax

namespace Salty.CByte

/-- Concatenate right-associated statement blocks, removing their terminal skip. -/
def appendStatements : Stmt → Stmt → Stmt
  | .skip, rest => rest
  | .seq first tail, rest => .seq first (appendStatements tail rest)
  | code, rest => .seq code rest

theorem appendStatements_exec {cfg : Config} {a b : Stmt} {s t u : State}
    (front : Exec cfg a s t) (back : Exec cfg b t u) : Exec cfg (appendStatements a b) s u := by
  induction a generalizing s t with
  | skip => cases front; exact back
  | seq first tail ihFirst ihTail =>
    cases front with
    | seq hf ht => exact .seq hf (ihTail ht back)
  | assign name value => exact .seq front back
  | effect op args => exact .seq front back
  | branch cond yes no ihYes ihNo => exact .seq front back
  | loop cond body ihBody => exact .seq front back

end Salty.CByte
