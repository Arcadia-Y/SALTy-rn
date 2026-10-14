import Salty.Model.CByteMachine
import Salty.Proofs.Core.CByte
import Salty.Proofs.Core.Behavior

/-! A total small-step machine for the extracted intrinsic language. A stack of
remaining statements makes loops executable without a fuel bound. Failed
expression evaluation, assertions, or memory accesses produce an explicit fault.
The return observation is the entire memory; these kernels return void. -/
namespace Salty.CByte

theorem Steps.trans {cfg : Config} {a b c : Control}
    (hab : Steps cfg a b) (hbc : Steps cfg b c) : Steps cfg a c := by
  induction hab with
  | refl => exact hbc
  | step h _ ih => exact .step h (ih hbc)

theorem Exec.steps {cfg : Config} {code : Stmt} {s t : State}
    (h : Exec cfg code s t) (rest : List Stmt) :
    Steps cfg ⟨code :: rest, s⟩ ⟨rest, t⟩ := by
  induction h generalizing rest with
  | skip => exact .step rfl .refl
  | assign he => exact .step (by simp [machine, he]) .refl
  | effect he hm => exact .step (by simp [machine, he, hm]) .refl
  | seq _ _ iha ihb => exact .step rfl ((iha _).trans (ihb rest))
  | yes he ht _ ih => exact .step (by simp [machine, he, ht]) (ih rest)
  | no he ht _ ih => exact .step (by simp [machine, he, ht]) (ih rest)
  | done he ht => exact .step (by simp [machine, he, ht]) .refl
  | more he ht _ _ ihb ihl =>
    exact .step (by simp [machine, he, ht]) ((ihb _).trans (ihl rest))

theorem Steps.terminates {cfg : Config} {a b : Control} {o : Outcome Memory Fault}
    (h : Steps cfg a b) (hb : (machine cfg).Terminates b o) :
    (machine cfg).Terminates a o := by
  induction h with
  | refl => exact hb
  | step hn _ ih =>
    obtain ⟨fuel, hf⟩ := ih hb
    exact ⟨fuel + 1, by simpa [Machine.run, hn] using hf⟩

theorem Exec.terminates {cfg : Config} {code : Stmt} {s t : State}
    (h : Exec cfg code s t) :
    (machine cfg).Terminates ⟨[code], s⟩ (.returned t.memory) := by
  apply (h.steps []).terminates
  exact ⟨1, rfl⟩

/-- The successful-execution relation entails the same shared outcome contract
used for every machine instance, including agreement on faults and divergence.
Totality on the caller domain rules both out; outside it no claim is made. -/
theorem Equivalent.behavior {cfg : Config} {a b : Stmt} {pre : State → Prop}
    (h : CByte.Equivalent cfg a b pre) :
    Salty.Equivalent (machine cfg) (machine cfg)
      (fun s => ⟨[a], s⟩) (fun s => ⟨[b], s⟩) pre := by
  intro s hs o
  obtain ⟨sa, sb, ha, hb, hm⟩ := h s hs
  have hta := ha.terminates
  have htb := hb.terminates
  constructor
  · intro ho
    have he := (machine cfg).terminal_unique ho hta
    rw [he, hm]
    exact htb
  · intro ho
    have he := (machine cfg).terminal_unique ho htb
    rw [he, ← hm]
    exact hta

end Salty.CByte
