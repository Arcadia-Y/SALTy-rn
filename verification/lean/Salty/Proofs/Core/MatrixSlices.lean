import Salty.Proofs.Core.MatrixPlan

namespace Salty.CByte

/-- A contiguous group of columns of the same matrix. Address arithmetic stays
modular; caller object bounds remain a separate obligation. -/
def MatrixCopy.slice (p : MatrixCopy) (start count : Nat) : MatrixCopy :=
  {p with input := p.input + BitVec.ofNat 64 (4 * start),
          output := p.output + BitVec.ofNat 64 (start * p.outputStride), cols := count}

theorem MatrixCopy.slice_readAddress (p : MatrixCopy) (start count r c : Nat) :
    (p.slice start count).readAddress (r,c) = p.readAddress (r,start+c) := by
  simp only [slice, readAddress, Nat.mul_add, BitVec.ofNat_add]
  ac_rfl

theorem MatrixCopy.slice_writeAddress (p : MatrixCopy) (start count r c : Nat) :
    (p.slice start count).writeAddress (r,c) = p.writeAddress (r,start+c) := by
  simp only [slice, writeAddress, Nat.add_mul, BitVec.ofNat_add]
  ac_rfl

theorem MatrixCopy.slice_separated (p : MatrixCopy) (start count : Nat)
    (bound : start + count ≤ p.cols) (sep : p.separated) : (p.slice start count).separated := by
  rintro ⟨ra,ca⟩ ⟨rb,cb⟩ ⟨hra,hca⟩ ⟨hrb,hcb⟩ hne address hleft hright
  have hca : ca < count := hca
  have hcb : cb < count := hcb
  apply sep (ra,start+ca) (rb,start+cb) ⟨hra, by omega⟩ ⟨hrb, by omega⟩
    (by intro h; apply hne; simpa using h) address
  · simpa only [slice_writeAddress] using hleft
  · simpa only [slice_writeAddress] using hright

/-- Fold whole columns while retaining the original input memory. -/
def MatrixCopy.columnFold (p : MatrixCopy) (original working : Memory)
    (start count : Nat) : Memory :=
  (List.range' start count).foldl (fun m c =>
    (List.range p.rows).foldl (fun m r => p.writeWord original m (r,c)) m) working

theorem MatrixCopy.columnFold_zero (p : MatrixCopy) (original working : Memory) (start : Nat) :
    p.columnFold original working start 0 = working := rfl

theorem MatrixCopy.columnFold_add (p : MatrixCopy) (original working : Memory)
    (start left right : Nat) :
    p.columnFold original working start (left + right) =
      p.columnFold original (p.columnFold original working start left) (start + left) right := by
  simp only [columnFold, ← List.range'_append_1, List.foldl_append]

private theorem columns_fold (p : MatrixCopy) (original working : Memory) :
    p.columnVisits.foldl (p.writeWord original) working = p.columnFold original working 0 p.cols := by
  have aux (cs : List Nat) (m : Memory) :
      (cs.flatMap (fun c => (List.range p.rows).map (fun r => (r,c)))).foldl
        (p.writeWord original) m =
      cs.foldl (fun m c => (List.range p.rows).foldl
        (fun m r => p.writeWord original m (r,c)) m) m := by
    induction cs generalizing m with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_map, List.foldl_cons]
      exact ih _
  simpa only [MatrixCopy.columnVisits, MatrixCopy.columnFold, List.range_eq_range'] using aux (List.range p.cols) working

theorem MatrixCopy.result_columnFold (p : MatrixCopy) (original : Memory) (sep : p.separated) :
    p.result original = p.columnFold original original 0 p.cols := by
  rw [p.row_column_agree original sep, columns_fold]

theorem MatrixCopy.slice_columnFold (p : MatrixCopy) (original working : Memory)
    (start count : Nat) :
    (p.slice start count).columnFold original working 0 count =
      p.columnFold original working start count := by
  have ranges : List.range' start count = (List.range' 0 count).map (start + ·) := by
    rw [List.map_add_range']
    simp
  simp only [columnFold, ranges, List.foldl_map, slice]
  congr 1
  funext m c
  congr 1
  funext m r
  change (p.slice start count).writeWord original m (r,c) = p.writeWord original m (r,start+c)
  simp only [writeWord, slice_readAddress, slice_writeAddress]

private theorem fold_congr {α β : Type} (xs : List α) (f g : β → α → β)
    (initial : β) (same : ∀ x ∈ xs, ∀ state, f state x = g state x) :
    xs.foldl f initial = xs.foldl g initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [same x (List.mem_cons_self ..) initial]
    exact ih _ (by intro y hy state; exact same y (List.mem_cons_of_mem _ hy) state)

theorem MatrixCopy.columnFold_original (p : MatrixCopy) (left right working : Memory)
    (start count : Nat)
    (same : ∀ r, r < p.rows → ∀ c, start ≤ c → c < start + count →
      readBytes left (p.readAddress (r,c)) 4 = readBytes right (p.readAddress (r,c)) 4) :
    p.columnFold left working start count = p.columnFold right working start count := by
  apply fold_congr
  intro c hc m
  have hc : start ≤ c ∧ c < start + count := by
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp hc
    omega
  apply fold_congr
  intro r hr m
  have hr : r < p.rows := by simpa using hr
  simp only [writeWord, same r hr c hc.1 hc.2]

/-- A strip result is the corresponding part of a column-ordered copy. The
input agreement premise refers only to bytes read, not to a desired output. -/
theorem MatrixCopy.slice_result (p : MatrixCopy) (original working : Memory)
    (start count : Nat) (bound : start + count ≤ p.cols) (sep : p.separated)
    (same : ∀ r, r < p.rows → ∀ c, start ≤ c → c < start + count →
      readBytes working (p.readAddress (r,c)) 4 = readBytes original (p.readAddress (r,c)) 4) :
    (p.slice start count).result working = p.columnFold original working start count := by
  rw [(p.slice start count).result_columnFold working (p.slice_separated start count bound sep)]
  change (p.slice start count).columnFold working working 0 count = _
  rw [p.slice_columnFold working working start count]
  exact p.columnFold_original working original working start count same

@[simp] theorem MatrixCopy.fold_readable (p : MatrixCopy) (original working : Memory)
    (visits : List (Nat × Nat)) :
    (visits.foldl (p.writeWord original) working).readable = working.readable := by
  induction visits generalizing working with
  | nil => rfl
  | cons rc rest ih => simp only [List.foldl_cons, ih, writeWord, writeBytes_readable]

@[simp] theorem MatrixCopy.fold_writable (p : MatrixCopy) (original working : Memory)
    (visits : List (Nat × Nat)) :
    (visits.foldl (p.writeWord original) working).writable = working.writable := by
  induction visits generalizing working with
  | nil => rfl
  | cons rc rest ih => simp only [List.foldl_cons, ih, writeWord, writeBytes_writable]

@[simp] theorem MatrixCopy.result_readable (p : MatrixCopy) (original : Memory) :
    (p.result original).readable = original.readable := p.fold_readable original original p.rowVisits

@[simp] theorem MatrixCopy.result_writable (p : MatrixCopy) (original : Memory) :
    (p.result original).writable = original.writable := p.fold_writable original original p.rowVisits

end Salty.CByte
