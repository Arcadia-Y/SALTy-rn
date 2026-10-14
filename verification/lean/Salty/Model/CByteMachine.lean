import Salty.Model.CByte
import Salty.Model.Behavior

/-! Review-facing definitions. Supporting lemmas live in `Salty.Proofs.Core.CByteMachine`. -/

/-! A total small-step machine for the extracted intrinsic language. A stack of
remaining statements makes loops executable without a fuel bound. Failed
expression evaluation, assertions, or memory accesses produce an explicit fault.
The return observation is the entire memory; these kernels return void. -/
namespace Salty.CByte

structure Control where
  pending : List Stmt
  state : State

inductive Fault where
  | invalidOperation
  deriving DecidableEq

def machine (cfg : Config) : Machine Control Memory Fault where
  next c := match c.pending with
    | [] => .inl (.returned c.state.memory)
    | stmt :: rest =>
      match stmt with
      | .skip => .inr ⟨rest, c.state⟩
      | .assign name e => match eval cfg c.state e with
        | some v => .inr ⟨rest, update c.state name v⟩
        | none => .inl (.fault .invalidOperation)
      | .effect op args => match args.mapM (eval cfg c.state) with
        | none => .inl (.fault .invalidOperation)
        | some vs => match effect c.state.memory op vs with
          | none => .inl (.fault .invalidOperation)
          | some m => .inr ⟨rest, {c.state with memory := m}⟩
      | .seq a b => .inr ⟨a :: b :: rest, c.state⟩
      | .branch e a b => match eval cfg c.state e >>= truth with
        | none => .inl (.fault .invalidOperation)
        | some test => .inr ⟨(if test then a else b) :: rest, c.state⟩
      | .loop e body => match eval cfg c.state e >>= truth with
        | none => .inl (.fault .invalidOperation)
        | some false => .inr ⟨rest, c.state⟩
        | some true => .inr ⟨body :: .loop e body :: rest, c.state⟩

/-- Finite machine transitions, with no bound fixed by the specification. -/
inductive Steps (cfg : Config) : Control → Control → Prop where
  | refl : Steps cfg c c
  | step : (machine cfg).next a = .inr b → Steps cfg b c → Steps cfg a c

end Salty.CByte
