import Salty.Proofs.Core.CByteMachine

namespace Salty.CByte

/-- Lift an independently established full-memory execution result to the
review-facing total-correctness predicate of the observable machine. -/
theorem totalCorrect_of_exec (cfg : Config) (code : Stmt) (pre : State → Prop) (spec : State → Memory)
    (execution : ∀ s, pre s → ∃ t, Exec cfg code s t ∧ t.memory = spec s) :
    Salty.TotalCorrect (machine cfg) (fun s => ⟨[code],s⟩) pre spec := by
  intro s h
  obtain ⟨t,run,result⟩ := execution s h
  have terminal := run.terminates
  rw [result] at terminal
  exact terminal

end Salty.CByte
