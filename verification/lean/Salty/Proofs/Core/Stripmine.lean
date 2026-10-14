import Std

namespace Salty

/-- An arbitrary positive chunk schedule. Hardware VSETVL obeys further bounds,
but the functional chunk theorem needs only progress; it does not assume VLMAX
is constant or VL is always the largest legal choice. -/
structure Schedule where
  choose : Nat → Nat
  progress : ∀ n, 0 < n → 0 < choose n

/-- Functional model of a pure pointwise loop. This is an intermediate lemma,
not a lifting of any C function. In particular, aliases and tail overreads must
be handled by a separate machine-to-list refinement proof. -/
def stripmine {A B : Type} (schedule : Schedule) (f : A → B) (input : List A) : List B :=
  if _h : input.length = 0 then []
  else
    let n := schedule.choose input.length
    (input.take n).map f ++ stripmine schedule f (input.drop n)
termination_by input.length
decreasing_by
  have hp : 0 < input.length := Nat.pos_of_ne_zero _h
  have hc := schedule.progress input.length hp
  simp only [List.length_drop]
  omega

/-- All lengths and all progressing schedules, with no finite maximum size. -/
theorem stripmine_eq_map {A B : Type} (schedule : Schedule) (f : A → B) (input : List A) :
    stripmine schedule f input = input.map f := by
  rw [stripmine]
  split
  · have he : input = [] := List.length_eq_zero_iff.mp ‹input.length = 0›
    subst input
    rfl
  · dsimp only
    rw [stripmine_eq_map schedule f (input.drop (schedule.choose input.length))]
    rw [← List.map_append, List.take_append_drop]
termination_by input.length
decreasing_by
  have hp : 0 < input.length := Nat.pos_of_ne_zero ‹input.length ≠ 0›
  have hc := schedule.progress input.length hp
  simp only [List.length_drop]
  omega

theorem stripmine_schedule_independent {A B : Type} (a b : Schedule) (f : A → B)
    (input : List A) : stripmine a f input = stripmine b f input := by
  rw [stripmine_eq_map, stripmine_eq_map]

end Salty
