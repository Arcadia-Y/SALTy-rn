import Std

/-! Review-facing definitions. Supporting lemmas live in `Salty.Proofs.Core.Behavior`. -/

/-! # A common observable-behavior contract

The machine state type is deliberately independent of the ISA. An observation
must include the caller-visible memory and return value; faults are outcomes,
not silently excluded executions. Instantiating this interface does not itself
establish correspondence with a C file or a binary.
-/
namespace Salty

inductive Outcome (Observation Fault : Type) where
  | returned : Observation → Outcome Observation Fault
  | fault : Fault → Outcome Observation Fault
  deriving DecidableEq

/-- A deterministic, total instruction transition: stop or take one step.
Unsupported instructions must fault, never return an arbitrary successful value.
Architectural nondeterminism must be resolved by an explicit machine parameter,
and a client theorem must quantify over all permitted resolutions. -/
structure Machine (State Observation Fault : Type) where
  next : State → Sum (Outcome Observation Fault) State

namespace Machine
variable {S O F : Type} (m : Machine S O F)

/-- Fuel is an executable observer, not a bound in the final specification. -/
def run : Nat → S → Option (Outcome O F)
  | 0, _ => none
  | n + 1, s => match m.next s with
    | .inl o => some o
    | .inr t => run n t

def Terminates (s : S) (o : Outcome O F) : Prop :=
  ∃ n, m.run n s = some o

/-- For a total deterministic transition, no finite terminal execution means
the execution continues indefinitely. This includes no bounded timeout case. -/
def Diverges (s : S) : Prop := ∀ n, m.run n s = none
end Machine

/-- One relation for NEON–NEON, RVV–RVV, and NEON–RVV. State encodings
may differ; outcomes use the same caller-visible observation type. -/
def Equivalent {S T I O F : Type}
    (left : Machine S O F) (right : Machine T O F)
    (initLeft : I → S) (initRight : I → T) (pre : I → Prop) : Prop :=
  ∀ i, pre i → ∀ o,
    left.Terminates (initLeft i) o ↔ right.Terminates (initRight i) o

def TotalCorrect {S I O F : Type} (m : Machine S O F)
    (init : I → S) (pre : I → Prop) (spec : I → O) : Prop :=
  ∀ i, pre i → m.Terminates (init i) (.returned (spec i))

end Salty
