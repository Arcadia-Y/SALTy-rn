import Salty.Proofs.Rsum.Correct
import Salty.Examples.Rsum

namespace Salty.Kernels.Rsum
open CByte ReductionISA

/-- The logical input starts at the output word. Its low byte is read before
that word is updated; the other readable bytes include arbitrary padding. -/
def witnessCall : Call := ⟨1, 16#64, 16#64, 32#64, 1#32⟩
def witnessState : State :=
  ⟨fun name => if name = "batch" then some (.integer 1)
    else if name = "input" then some (.pointer 16#64)
    else if name = "output" then some (.pointer 16#64)
    else if name = "params" then some (.pointer 32#64) else none,
   ⟨fun a => if a = 16#64 then 1 else if a = 17#64 ∨ a = 18#64 ∨ a = 19#64 then 0 else 213,
    fun _ => true, fun _ => true⟩⟩

theorem entry_nonempty (kind : Interpretation) : Entry kind witnessState witnessCall := by
  constructor
  all_goals try { rfl }
  all_goals try { decide }
  · intro a ha; rfl
  · intro a ha; rfl
  · intro a ha; rfl
  · cases kind <;> unfold OutputDefined <;> decide

theorem witness_overlap : witnessCall.input = witnessCall.output := rfl

theorem witness_result (kind : Interpretation) :
    (resultMemory kind witnessState.memory witnessCall).data 16#64 = 2 := by
  cases kind <;> decide

/-- The unsigned scalar update wraps while the corresponding signed overflowing
update is excluded by its explicit definedness predicate. -/
theorem witness_unsigned_wrap : outputScalar .unsigned (4294967295#32) (1#32) = 0 := by decide

theorem witness_signed_overflow : ¬ OutputDefined .signed (2147483647#32) (1#32) := by unfold OutputDefined; decide

theorem witness_capacity : 8 ≤ (RsumExamples.config 32 (by decide) true).capacity := by decide

end Salty.Kernels.Rsum
