import Salty.Proofs.Rdsum.RvvData

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

def rvvIncrements (kind : Interpretation) : Stmt := dropStatements 20 (rvvGroup kind)

def pointersAfter (s : State) (pointers : Nat → Address) (increment : Nat) : State :=
  let s := update s "i0" (.pointer (pointers 0+BitVec.ofNat 64 increment))
  let s := update s "i1" (.pointer (pointers 1+BitVec.ofNat 64 increment))
  let s := update s "i2" (.pointer (pointers 2+BitVec.ofNat 64 increment))
  let s := update s "i3" (.pointer (pointers 3+BitVec.ofNat 64 increment))
  let s := update s "i4" (.pointer (pointers 4+BitVec.ofNat 64 increment))
  let s := update s "i5" (.pointer (pointers 5+BitVec.ofNat 64 increment))
  let s := update s "i6" (.pointer (pointers 6+BitVec.ofNat 64 increment))
  s

theorem rvv_increments_exec (kind : Interpretation) (cfg : Config) (s : State)
    (pointers : Nat → Address) (increment : Nat)
    (ptr : ∀ i, i < 7 → s.locals (rowName i) = some (.pointer (pointers i)))
    (step : s.locals "input_increment" = some (.integer increment)) :
    Exec cfg (rvvIncrements kind) s (pointersAfter s pointers increment) := by
  have cast (a : Address) :
      BitVec.ofInt 64 (convert .u64 ((a.toNat : Int)+increment)) = a+BitVec.ofNat 64 increment := by
    simp only [convert, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_natCast]
    simp
  have p0 := ptr 0 (by decide)
  have p1 := ptr 1 (by decide)
  have p2 := ptr 2 (by decide)
  have p3 := ptr 3 (by decide)
  have p4 := ptr 4 (by decide)
  have p5 := ptr 5 (by decide)
  have p6 := ptr 6 (by decide)
  simp only [rowName] at p0 p1 p2 p3 p4 p5 p6
  cases kind <;> apply run_sound (fuel := 10) <;>
    simp [rvvIncrements, rvvGroup, rvvBatches, rvvChannels, rvvProgram,
      Generated.QS8Rdsum.rvv, Generated.QU8Rdsum.rvv, dropStatements, firstStatement,
      takeStatements, loopBody, pointersAfter, run, eval, binary, cast,
      update_locals, update_memory, step,p0,p1,p2,p3,p4,p5,p6]

@[simp] theorem pointersAfter_memory (s : State) (pointers : Nat → Address) (increment : Nat) :
    (pointersAfter s pointers increment).memory = s.memory := rfl

theorem pointersAfter_row (s : State) (pointers : Nat → Address) (increment i : Nat) (hi : i < 7) :
    (pointersAfter s pointers increment).locals (rowName i) =
      some (.pointer (pointers i+BitVec.ofNat 64 increment)) := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [pointersAfter, update_locals, rowName]

end Salty.Kernels.Rdsum
