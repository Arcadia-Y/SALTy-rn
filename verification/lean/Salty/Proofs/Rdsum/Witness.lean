import Salty.Proofs.Rdsum.SpecLemmas

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- Eight rows cross the seven-row boundary; three columns exercise 2/1 stores.
A high-bit first byte distinguishes signed and unsigned interpretations. -/
def witnessCall : Call := ⟨8,3,16#64,16,256#64,512#64,0#64⟩

def witnessState : State :=
  ⟨fun name =>
    if name = "rows" then some (.integer 8)
    else if name = "channels" then some (.integer 3)
    else if name = "input" then some (.pointer 16#64)
    else if name = "input_stride" then some (.integer 16)
    else if name = "zero" then some (.pointer 256#64)
    else if name = "output" then some (.pointer 512#64)
    else if name = "params" then some (.pointer 0#64)
    else none,
   ⟨fun a => if a = 16#64 then 255 else 0, fun _ => true, fun _ => true⟩⟩

theorem entry_nonempty (kind : Interpretation) : Entry kind witnessState witnessCall := by
  constructor
  all_goals try rfl
  all_goals try decide
  · intro row hr a ha; rfl
  · intro a ha; rfl
  · intro a ha
    have neq : a ≠ 16#64 := by
      obtain ⟨i,hi,he⟩ := ha
      intro eq
      have value := congrArg BitVec.toNat (he.symm.trans eq)
      simp [witnessCall, BitVec.toNat_add, BitVec.toNat_ofNat] at value hi
      omega
    simp [witnessState, neq]
  · intro a ha; rfl
  · intro a ha; rfl
  · intro row hr a ha hb
    obtain ⟨i,hi,he⟩ := ha
    obtain ⟨j,hj,hf⟩ := hb
    have value := congrArg BitVec.toNat (he.symm.trans hf)
    simp [witnessCall, BitVec.toNat_add, BitVec.toNat_ofNat] at value hr hi hj
    omega
  · intro a ha hb
    obtain ⟨i,hi,he⟩ := ha
    obtain ⟨j,hj,hf⟩ := hb
    have value := congrArg BitVec.toNat (he.symm.trans hf)
    simp [witnessCall, BitVec.toNat_add, BitVec.toNat_ofNat] at value hi hj
    omega
  · cases kind <;> unfold ScalarTailDefined <;> decide

theorem witness_signed_result :
    (resultMemory .signed witnessState.memory witnessCall).data 513#64 = 255 := by decide

theorem witness_unsigned_result :
    (resultMemory .unsigned witnessState.memory witnessCall).data 513#64 = 0 := by decide

end Salty.Kernels.Rdsum
