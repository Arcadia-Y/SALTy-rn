import Salty.Model.Behavior
import Std

/-! # A common observable-behavior contract

The machine state type is deliberately independent of the ISA. An observation
must include the caller-visible memory and return value; faults are outcomes,
not silently excluded executions. Instantiating this interface does not itself
establish correspondence with a C file or a binary.
-/
namespace Salty

namespace Machine
variable {S O F : Type} (m : Machine S O F)

theorem run_mono {n : Nat} {s : S} {o : Outcome O F}
    (h : m.run n s = some o) (k : Nat) : m.run (n + k) s = some o := by
  induction n generalizing s with
  | zero => simp [run] at h
  | succ n ih =>
    cases hn : m.next s with
    | inl x => simpa [run, hn, Nat.succ_add] using h
    | inr t =>
      simp only [run, hn] at h
      simpa [run, hn, Nat.succ_add] using ih h

theorem terminal_unique {s : S} {a b : Outcome O F}
    (ha : m.Terminates s a) (hb : m.Terminates s b) : a = b := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨k, hk⟩ := hb
  have h₁ := m.run_mono hn k
  have h₂ := m.run_mono hk n
  rw [Nat.add_comm k n, h₁] at h₂
  exact Option.some.inj h₂

theorem diverges_iff (s : S) : m.Diverges s ↔ ¬ ∃ o, m.Terminates s o := by
  constructor
  · intro h ⟨o, n, hn⟩
    have := h n
    rw [hn] at this
    contradiction
  · intro h n
    cases hn : m.run n s with
    | none => rfl
    | some o => exact False.elim (h ⟨o, n, hn⟩)
end Machine

theorem Equivalent.divergence {S T I O F : Type}
    {left : Machine S O F} {right : Machine T O F}
    {il : I → S} {ir : I → T} {pre : I → Prop}
    (h : Equivalent left right il ir pre) (i : I) (hi : pre i) :
    left.Diverges (il i) ↔ right.Diverges (ir i) := by
  rw [Machine.diverges_iff, Machine.diverges_iff]
  exact not_congr (exists_congr (h i hi))

/-- Independent proofs against a shared specification establish equivalence.
The premises are actual termination proofs, not assumed equivalence. -/
theorem equivalent_of_correct {S T I O F : Type}
    {left : Machine S O F} {right : Machine T O F}
    {il : I → S} {ir : I → T} {pre : I → Prop} {spec : I → O}
    (hl : TotalCorrect left il pre spec)
    (hr : TotalCorrect right ir pre spec) : Equivalent left right il ir pre := by
  intro i hi o
  constructor
  · intro ho
    have he := left.terminal_unique ho (hl i hi)
    rw [he]
    exact hr i hi
  · intro ho
    have he := right.terminal_unique ho (hr i hi)
    rw [he]
    exact hl i hi

end Salty
