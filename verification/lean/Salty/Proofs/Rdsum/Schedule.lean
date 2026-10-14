import Salty.Proofs.Rdsum.BatchSafety

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- A row's original byte at each column after the actual zero-pointer choice. -/
def selectedRow (m : Memory) (pointers : Nat → Address) (zero : Address) (remaining : Int)
    (row column : Nat) : Byte :=
  m.data (selectedPointers pointers remaining zero row+BitVec.ofNat 64 column)

/-- Row functions visited by the actual batch schedule, including substituted
zero rows. This is independent of the accumulator and vector instruction model. -/
def scheduledRows (m : Memory) (zero : Address) (increment : Nat) :
    Nat → (Nat → Address) → Int → List (Nat → Byte)
  | 0, _, _ => []
  | count+1, pointers, remaining =>
      (List.range 7).map (selectedRow m pointers zero remaining) ++
      scheduledRows m zero increment count (groupPointers pointers zero remaining increment) (remaining-7)

@[simp] theorem scheduledRows_length (m : Memory) (zero : Address) (increment count : Nat)
    (pointers : Nat → Address) (remaining : Int) :
    (scheduledRows m zero increment count pointers remaining).length = 7*count := by
  induction count generalizing pointers remaining with
  | zero => rfl
  | succ count ih => simp [scheduledRows, ih]; omega

theorem rowAcc_selected (kind : Interpretation) (m : Memory) (pointers : Nat → Address)
    (zero : Address) (remaining : Int) (width : Nat) (initial : List (BitVec 16)) :
    rowAcc kind (groupRows m pointers zero remaining width) initial 7 =
      ((List.range 7).map (selectedRow m pointers zero remaining)).foldl
        (fun acc row => WideningISA.widenAdd16 kind acc ((List.range width).map row)) initial := by
  rw [rowAcc_fold, List.foldl_map]
  congr 1
  funext acc i
  unfold groupRows
  rw [readBytes_columns]
  rfl

/-- The actual loop's accumulated halfwords are the fold over its selected
original-memory row functions. This retains row order and all padding rows. -/
theorem groupFold_schedule (kind : Interpretation) (m : Memory) (zero : Address) (width increment count : Nat)
    (pointers : Nat → Address) (remaining : Int) (initial : List (BitVec 16)) :
    (groupFold kind m zero width increment count pointers remaining initial).acc =
      (scheduledRows m zero increment count pointers remaining).foldl
        (fun acc row => WideningISA.widenAdd16 kind acc ((List.range width).map row)) initial := by
  induction count generalizing pointers remaining initial with
  | zero => rfl
  | succ count ih =>
    simp only [groupFold, scheduledRows, List.foldl_append, ih, rowAcc_selected]

/-- A reset batch of at most 256 selected rows widens to one modular word sum
per column. The kernels' largest batch has 36*7=252 rows. -/
theorem widen_groupFold (kind : Interpretation) (m : Memory) (zero : Address) (width increment count : Nat)
    (pointers : Nat → Address) (remaining : Int) (initial : Nat → BitVec 32)
    (small : 7*count ≤ 256) :
    WideningISA.widenAdd32 kind ((List.range width).map initial)
      (groupFold kind m zero width increment count pointers remaining
        ((List.range width).map (fun _ => 0))).acc =
      (List.range width).map (fun column => initial column +
        sumWords (widen32 kind ((scheduledRows m zero increment count pointers remaining).map
          (fun row => row column)))) := by
  rw [groupFold_schedule]
  exact WideningISA.widen_rows kind (List.range width) _ initial (by simpa using small)

end Salty.Kernels.Rdsum
