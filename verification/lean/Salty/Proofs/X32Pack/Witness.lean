import Salty.Proofs.X32Pack.Correct
import Salty.Examples.X32Pack

namespace Salty.Kernels.X32Pack
open CByte

/-- Two groups with three channels each exercise paired and odd tiles. Bias is
optional, extra gaps are nonzero, and an odd scalar weight has its high bit set. -/
def witnessCall (withBias : Bool) : Call := ⟨2,3,1,16#64,if withBias then 128#64 else 0#64,512#64,4,0,0⟩

def witnessState (withBias : Bool) : State :=
  ⟨fun name =>
    if name = "g" then some (.integer 2)
    else if name = "nc" then some (.integer 3)
    else if name = "kc" then some (.integer 1)
    else if name = "nr" then some (.integer 2)
    else if name = "kr" ∨ name = "sr" then some (.integer 1)
    else if name = "weights" then some (.pointer 16#64)
    else if name = "bias" then some (.pointer (if withBias then 128#64 else 0#64))
    else if name = "packed_weights" then some (.pointer 512#64)
    else if name = "extra_bytes" then some (.integer 4)
    else if name = "scale" ∨ name = "params" then some (.pointer 0#64)
    else none,
   ⟨fun a => if a = 24#64 then 255 else 165, fun _ => true, fun _ => true⟩⟩

private theorem witness_disjoint (input : Address) (low : input = 16#64 ∨ input = 128#64)
    (a : Address) (left : Footprint input 24 a) (right : Footprint 512#64 80 a) : False := by
  obtain ⟨i, hi, he⟩ := left
  obtain ⟨j, hj, hf⟩ := right
  have hn := congrArg BitVec.toNat (he.symm.trans hf)
  rcases low with rfl | rfl <;> simp [BitVec.toNat_add, BitVec.toNat_ofNat] at hn <;> omega

theorem entry_nonempty (withBias : Bool) : Entry (witnessState withBias) (witnessCall withBias) := by
  cases withBias <;> constructor
  all_goals try rfl
  all_goals try decide
  all_goals try { intro _; decide }
  all_goals try { intro a ha; rfl }
  all_goals try { intro hn a ha; rfl }
  all_goals try { intro hn; contradiction }
  all_goals try { intro a ha hb; exact witness_disjoint _ (Or.inl rfl) a ha hb }
  · intro hn a ha hb
    exact witness_disjoint _ (Or.inr rfl) a ha hb

def witnessResult (withBias : Bool) : Memory :=
  packGroups 3 1 4 2 (witnessState withBias).memory 16#64 (if withBias then 128#64 else 0#64) 512#64

theorem witness_null_header : (witnessResult false).data 536#64 = 0 := by decide

theorem witness_present_header_hole : (witnessResult true).data 536#64 = 165 := by decide

theorem witness_odd_weight (withBias : Bool) : (witnessResult withBias).data 540#64 = 255 := by cases withBias <;> decide

theorem witness_weight_hole (withBias : Bool) : (witnessResult withBias).data 544#64 = 165 := by cases withBias <;> decide

theorem witness_extra_gap (withBias : Bool) : (witnessResult withBias).data 548#64 = 165 := by cases withBias <;> decide

theorem witness_capacity : 8 ≤ (RsumExamples.config 16 (by decide) true).capacity := by decide

end Salty.Kernels.X32Pack
