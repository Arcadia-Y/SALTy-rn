import Salty.Proofs.Core.Behavior

namespace Salty
namespace Machine
variable {S O F : Type} (m : Machine S O F)

/-- A finite instruction path with no terminal transition. -/
inductive Steps : Nat → S → S → Prop where
  | zero (s) : Steps 0 s s
  | succ {n s t u} : m.next s = .inr t → Steps n t u → Steps (n + 1) s u

theorem run_prefix {n : Nat} {s t : S} (h : m.Steps n s t) (k : Nat) :
    m.run (n + k) s = m.run k t := by
  induction h with
  | zero => simp
  | succ hn _ ih => simpa [run, hn, Nat.succ_add] using ih

theorem terminates_prefix {n : Nat} {s t : S} {o : Outcome O F}
    (h : m.Steps n s t) (ht : m.Terminates t o) : m.Terminates s o := by
  obtain ⟨k, hk⟩ := ht
  exact ⟨n + k, (m.run_prefix h k).trans hk⟩
end Machine

/-- A forward simulation may match one source instruction with any finite
target path. Two such simulations prove equality of terminal behaviors;
determinism and total transitions then give divergence equivalence as well.
This handles different loop widths without imposing a global fuel bound. -/
structure Simulation {S T O F : Type} (left : Machine S O F)
    (right : Machine T O F) (rel : S → T → Prop) : Prop where
  terminal : ∀ s t o, rel s t → left.next s = .inl o → right.Terminates t o
  step : ∀ s t s', rel s t → left.next s = .inr s' →
    ∃ n t', right.Steps n t t' ∧ rel s' t'

theorem Simulation.preserves {S T O F : Type}
    {left : Machine S O F} {right : Machine T O F} {rel : S → T → Prop}
    (sim : Simulation left right rel) {s : S} {t : T} {o : Outcome O F}
    (hrel : rel s t) (halt : left.Terminates s o) : right.Terminates t o := by
  obtain ⟨n, hn⟩ := halt
  induction n generalizing s t with
  | zero => simp [Machine.run] at hn
  | succ n ih =>
    cases he : left.next s with
    | inl result =>
      simp only [Machine.run, he, Option.some.injEq] at hn
      subst result
      exact sim.terminal s t o hrel he
    | inr s' =>
      obtain ⟨k, t', hp, hr⟩ := sim.step s t s' hrel he
      exact right.terminates_prefix hp (ih hr (by simpa [Machine.run, he] using hn))

theorem equivalent_of_simulations {S T I O F : Type}
    {left : Machine S O F} {right : Machine T O F}
    {il : I → S} {ir : I → T} {pre : I → Prop}
    {lr : S → T → Prop} {rl : T → S → Prop}
    (forward : Simulation left right lr) (backward : Simulation right left rl)
    (initial : ∀ i, pre i → lr (il i) (ir i) ∧ rl (ir i) (il i)) :
    Equivalent left right il ir pre := by
  intro i hi o
  exact ⟨forward.preserves (initial i hi).1, backward.preserves (initial i hi).2⟩

end Salty
