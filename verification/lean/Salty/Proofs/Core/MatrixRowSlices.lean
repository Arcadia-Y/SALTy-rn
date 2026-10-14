import Salty.Proofs.Core.MatrixSlices

namespace Salty.CByte

/-- Row partitions support fixed-height NEON tiles just as column partitions
support variable-width RVV strips. Both refer to the same matrix word copies. -/
def MatrixCopy.rowSlice (p : MatrixCopy) (start count : Nat) : MatrixCopy :=
  {p with input := p.input + BitVec.ofNat 64 (start * p.inputStride),
          output := p.output + BitVec.ofNat 64 (4 * start), rows := count}

theorem MatrixCopy.rowSlice_compose (p : MatrixCopy) (a b c d : Nat) :
    (p.rowSlice a b).rowSlice c d = p.rowSlice (a+c) d := by
  simp only [rowSlice, Nat.add_mul, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

theorem MatrixCopy.rowSlice_readAddress (p : MatrixCopy) (start count r c : Nat) :
    (p.rowSlice start count).readAddress (r,c) = p.readAddress (start+r,c) := by
  simp only [rowSlice, readAddress, Nat.add_mul, BitVec.ofNat_add]
  ac_rfl

theorem MatrixCopy.rowSlice_writeAddress (p : MatrixCopy) (start count r c : Nat) :
    (p.rowSlice start count).writeAddress (r,c) = p.writeAddress (start+r,c) := by
  simp only [rowSlice, writeAddress, Nat.mul_add, BitVec.ofNat_add]
  ac_rfl

theorem MatrixCopy.rowSlice_separated (p : MatrixCopy) (start count : Nat)
    (bound : start+count ≤ p.rows) (sep : p.separated) : (p.rowSlice start count).separated := by
  rintro ⟨ra,ca⟩ ⟨rb,cb⟩ ⟨hra,hca⟩ ⟨hrb,hcb⟩ hne address hleft hright
  have hra : ra < count := hra
  have hrb : rb < count := hrb
  apply sep (start+ra,ca) (start+rb,cb) ⟨by omega,hca⟩ ⟨by omega,hcb⟩
    (by intro h; apply hne; simpa using h) address
  · simpa only [rowSlice_writeAddress] using hleft
  · simpa only [rowSlice_writeAddress] using hright

def MatrixCopy.rowFold (p : MatrixCopy) (original working : Memory)
    (start count : Nat) : Memory :=
  (List.range' start count).foldl (p.writeRow original) working

theorem MatrixCopy.rowFold_add (p : MatrixCopy) (original working : Memory)
    (start left right : Nat) :
    p.rowFold original working start (left+right) =
      p.rowFold original (p.rowFold original working start left) (start+left) right := by
  simp only [rowFold, ← List.range'_append_1, List.foldl_append]

theorem MatrixCopy.result_rowFold (p : MatrixCopy) (original : Memory) :
    p.result original = p.rowFold original original 0 p.rows := by
  unfold result
  rw [← p.rows_fold original original]
  simp only [rowFold, List.range_eq_range']

theorem MatrixCopy.rowSlice_rowFold (p : MatrixCopy) (original working : Memory)
    (start count : Nat) :
    (p.rowSlice start count).rowFold original working 0 count =
      p.rowFold original working start count := by
  have ranges : List.range' start count = (List.range' 0 count).map (start + ·) := by
    rw [List.map_add_range']
    simp
  simp only [rowFold, ranges, List.foldl_map]
  congr 1
  funext m r
  simp only [writeRow, rowSlice]
  congr 1
  funext m c
  change (p.rowSlice start count).writeWord original m (r,c) = p.writeWord original m (start+r,c)
  simp only [writeWord, rowSlice_readAddress, rowSlice_writeAddress]

private theorem fold_congr {α β : Type} (xs : List α) (f g : β → α → β)
    (initial : β) (same : ∀ x ∈ xs, ∀ state, f state x = g state x) :
    xs.foldl f initial = xs.foldl g initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [same x (List.mem_cons_self ..) initial]
    exact ih _ (by intro y hy state; exact same y (List.mem_cons_of_mem _ hy) state)

theorem MatrixCopy.rowFold_original (p : MatrixCopy) (left right working : Memory)
    (start count : Nat)
    (same : ∀ r, start ≤ r → r < start+count → ∀ c, c < p.cols →
      readBytes left (p.readAddress (r,c)) 4 = readBytes right (p.readAddress (r,c)) 4) :
    p.rowFold left working start count = p.rowFold right working start count := by
  apply fold_congr
  intro r hr m
  have hr : start ≤ r ∧ r < start+count := by
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp hr
    omega
  apply fold_congr
  intro c hc m
  have hc : c < p.cols := by simpa using hc
  simp only [writeWord, same r hr.1 hr.2 c hc]

theorem MatrixCopy.rowSlice_result (p : MatrixCopy) (original working : Memory)
    (start count : Nat)
    (same : ∀ r, start ≤ r → r < start+count → ∀ c, c < p.cols →
      readBytes working (p.readAddress (r,c)) 4 = readBytes original (p.readAddress (r,c)) 4) :
    (p.rowSlice start count).result working = p.rowFold original working start count := by
  rw [(p.rowSlice start count).result_rowFold working]
  change (p.rowSlice start count).rowFold working working 0 count = _
  rw [p.rowSlice_rowFold working working start count]
  exact p.rowFold_original working original working start count same

end Salty.CByte
