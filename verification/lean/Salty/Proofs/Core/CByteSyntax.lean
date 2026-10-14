import Salty.Proofs.Core.CByte

namespace Salty.CByte

/-- Syntactic projections retain exact generated statements for block proofs. -/
def dropStatements : Nat → Stmt → Stmt
  | 0, code => code
  | n + 1, .seq _ rest => dropStatements n rest
  | _, _ => .skip

def firstStatement : Stmt → Stmt
  | .seq first _ => first
  | code => code

def loopBody : Stmt → Stmt
  | .loop _ body => body
  | _ => .skip

def takeStatements : Nat → Stmt → Stmt
  | 0, _ => .skip
  | n + 1, .seq first rest => .seq first (takeStatements n rest)
  | _ + 1, code => code

theorem exec_take_drop {cfg : Config} {code : Stmt} {s t u : State} (n : Nat)
    (front : Exec cfg (takeStatements n code) s t)
    (back : Exec cfg (dropStatements n code) t u) : Exec cfg code s u := by
  induction n generalizing code s t u with
  | zero => cases front; exact back
  | succ n ih =>
    cases code with
    | seq a b =>
      cases front with
      | seq ha hb => exact .seq ha (ih hb back)
    | skip => cases back; exact front
    | assign name e => cases back; exact front
    | effect op args => cases back; exact front
    | branch e a b => cases back; exact front
    | loop e body => cases back; exact front

theorem cast_nat (n : Nat) (h : n < 2^64) : convert .u64 n = n := by
  simp [convert, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem cast_sub (n k : Nat) (hk : k ≤ n) (hn : n < 2^64) :
    convert .u64 ((n : Int) - k) = (n - k : Nat) := by
  rw [← Int.natCast_sub hk]
  exact cast_nat _ (by omega)


/-- An executable syntactic write-set query. Effect primitives modify memory,
not local variables; expression evaluation has no local side effects. -/
def Stmt.writes (name : String) : Stmt → Bool
  | .skip => false
  | .assign target _ => name == target
  | .effect _ _ => false
  | .seq a b => a.writes name || b.writes name
  | .branch _ a b => a.writes name || b.writes name
  | .loop _ body => body.writes name

theorem Exec.locals_frame {cfg : Config} {code : Stmt} {s t : State}
    (h : Exec cfg code s t) (name : String) (untouched : code.writes name = false) :
    t.locals name = s.locals name := by
  induction h with
  | skip => rfl
  | assign he =>
    simp only [Stmt.writes, beq_eq_false_iff_ne] at untouched
    simp [update, untouched]
  | effect he hm => rfl
  | seq ha hb iha ihb =>
    simp only [Stmt.writes, Bool.or_eq_false_iff] at untouched
    exact (ihb untouched.2).trans (iha untouched.1)
  | yes he ht ha ih =>
    simp only [Stmt.writes, Bool.or_eq_false_iff] at untouched
    exact ih untouched.1
  | no he ht hb ih =>
    simp only [Stmt.writes, Bool.or_eq_false_iff] at untouched
    exact ih untouched.2
  | done he ht => rfl
  | more he ht hb hl ihb ihl =>
    exact (ihl untouched).trans (ihb untouched)

end Salty.CByte
