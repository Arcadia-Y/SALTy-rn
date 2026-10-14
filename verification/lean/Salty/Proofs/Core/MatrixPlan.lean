import Salty.Spec.MatrixLayout
import Salty.Proofs.Core.CWordMemory

/-! A common word-copy specification for matrix transpose. Loop order is not
observable when output words are disjoint. Relating extracted whole functions
to this specification remains a per-kernel proof obligation. -/
namespace Salty.CByte

private theorem map_append_flatMap_perm {α β : Type} (xs : List α)
    (f : α → β) (g : α → List β) :
    (xs.map f ++ xs.flatMap g).Perm (xs.flatMap (fun x => f x :: g x)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.flatMap_cons, List.cons_append]
    apply List.Perm.cons
    exact (List.perm_append_comm_assoc (xs.map f) (g x) (xs.flatMap g)).trans
      (ih.append_left (g x))

/-- Interchanging nested finite loops permutes their coordinate visits. -/
theorem matrix_visits_permute {α β γ : Type} (rows : List α) (cols : List β)
    (f : α → β → γ) :
    (rows.flatMap (fun r => cols.map (f r))).Perm
      (cols.flatMap (fun c => rows.map (fun r => f r c))) := by
  induction rows with
  | nil => simp
  | cons r rows ih =>
    simp only [List.flatMap_cons, List.map_cons]
    exact (ih.append_left (cols.map (f r))).trans
      (map_append_flatMap_perm cols (f r) (fun c => rows.map (fun r => f r c)))

theorem MatrixCopy.visit_valid (p : MatrixCopy) (rc : Nat × Nat) (h : rc ∈ p.rowVisits) :
    p.valid rc := by
  simp only [rowVisits, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨r, hr, c, hc, he⟩ := h
  cases he
  exact ⟨hr, hc⟩

theorem MatrixCopy.order_independent (p : MatrixCopy) (original working : Memory)
    (left right : List (Nat × Nat)) (sep : p.separated)
    (valid : ∀ rc ∈ left, p.valid rc) (perm : left.Perm right) :
    left.foldl (p.writeWord original) working = right.foldl (p.writeWord original) working := by
  apply perm.foldl_eq'
  intro a ha b hb m
  by_cases same : a = b
  · subst b; rfl
  · apply writeBytes_comm
    intro address hleft hright
    exact sep a b (valid a ha) (valid b hb) same address
      (by simpa using hleft) (by simpa using hright)

theorem MatrixCopy.row_column_agree (p : MatrixCopy) (original : Memory) (sep : p.separated) :
    p.result original = p.columnVisits.foldl (p.writeWord original) original := by
  apply p.order_independent original original p.rowVisits p.columnVisits sep
  · exact p.visit_valid
  · exact matrix_visits_permute (List.range p.rows) (List.range p.cols) (fun r c => (r,c))

theorem MatrixCopy.DestinationLayout.separated {p : MatrixCopy}
    (layout : p.DestinationLayout) : p.separated := by
  rintro ⟨ra, ca⟩ ⟨rb, cb⟩ ⟨hra, hca⟩ ⟨hrb, hcb⟩ hne address
    ⟨ia, hia, hea⟩ ⟨ib, hib, heb⟩
  have bound (r c i : Nat) (hr : r < p.rows) (hc : c < p.cols) (hi : i < 4) :
      c * p.outputStride + 4 * r + i < 2^64 := by
    have hm := Nat.mul_le_mul_right p.outputStride (show c ≤ p.cols - 1 by omega)
    have := layout.extent
    omega
  have ba := bound ra ca ia hra hca hia
  have bb := bound rb cb ib hrb hcb hib
  have reshape (r c i : Nat) :
      p.writeAddress (r,c) + BitVec.ofNat 64 i =
        p.output + BitVec.ofNat 64 (c * p.outputStride + 4 * r + i) := by
    simp only [writeAddress, BitVec.ofNat_add, BitVec.add_assoc]
  have he := hea.symm.trans heb
  rw [reshape ra ca ia, reshape rb cb ib] at he
  have hn := congrArg BitVec.toNat ((BitVec.add_right_inj p.output).mp he)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ba, Nat.mod_eq_of_lt bb] at hn
  by_cases same : ca = cb
  · subst cb
    have hrne : ra ≠ rb := by intro hr; apply hne; cases hr; rfl
    omega
  · have hs : 4 * p.rows ≤ p.outputStride := by
      rcases layout.stride with small | wide
      · omega
      · exact wide
    by_cases order : ca < cb
    · have hm := Nat.mul_le_mul_right p.outputStride (show ca + 1 ≤ cb by omega)
      simp only [Nat.add_mul, Nat.one_mul] at hm
      omega
    · have hm := Nat.mul_le_mul_right p.outputStride (show cb + 1 ≤ ca by omega)
      simp only [Nat.add_mul, Nat.one_mul] at hm
      omega

theorem MatrixCopy.visits_frame (p : MatrixCopy) (original working : Memory)
    (visits : List (Nat × Nat)) (address : Address)
    (outside : ∀ rc ∈ visits, ¬ Footprint (p.writeAddress rc) 4 address) :
    (visits.foldl (p.writeWord original) working).data address = working.data address := by
  induction visits generalizing working with
  | nil => rfl
  | cons rc rest ih =>
    rw [List.foldl_cons, ih _ (by intro x hx; exact outside x (List.mem_cons_of_mem _ hx))]
    apply writeBytes_frame
    simpa only [readBytes_length] using outside rc (List.mem_cons_self ..)

theorem MatrixCopy.result_frame (p : MatrixCopy) (original : Memory) (address : Address)
    (outside : ¬ p.footprint address) : (p.result original).data address = original.data address := by
  apply p.visits_frame
  intro rc hrc hp
  exact outside ⟨rc, p.visit_valid rc hrc, hp⟩

private theorem foldl_congr_on {α β : Type} (xs : List α) (f g : β → α → β)
    (initial : β) (same : ∀ x ∈ xs, ∀ state, f state x = g state x) :
    xs.foldl f initial = xs.foldl g initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [same x (List.mem_cons_self ..) initial]
    exact ih _ (by intro y hy state; exact same y (List.mem_cons_of_mem _ hy) state)

/-- One actual vector load plus strided-store effect refines the common
per-word matrix specification. The original input bytes are explicit. -/
theorem MatrixCopy.strided_writeRow (p : MatrixCopy) (original working : Memory) (row : Nat) :
    writeStrided32 working (p.output + BitVec.ofNat 64 (4 * row))
      (BitVec.ofNat 64 p.outputStride)
      (readBytes original (p.input + BitVec.ofNat 64 (row * p.inputStride)) (4 * p.cols)) p.cols =
      p.writeRow original working row := by
  rw [writeStrided32_lane_order]
  apply foldl_congr_on
  intro col hcol mem
  have hcol : col < p.cols := by simpa using hcol
  have hi : p.readAddress (row,col) =
      (p.input + BitVec.ofNat 64 (row * p.inputStride)) + BitVec.ofNat 64 (4 * col) := by
    simp [readAddress, BitVec.ofNat_add, BitVec.add_assoc]
  have ho : p.writeAddress (row,col) =
      (p.output + BitVec.ofNat 64 (4 * row)) + BitVec.ofNat 64 p.outputStride * BitVec.ofNat 64 col := by
    simp only [writeAddress, BitVec.ofNat_add, BitVec.ofNat_mul]
    rw [BitVec.mul_comm (BitVec.ofNat 64 col)]
    ac_rfl
  simp only [writeLane32, writeWord, hi, ho,
    readBytes_slice original (p.input + BitVec.ofNat 64 (row * p.inputStride))
      (4 * col) (4 * p.cols) 4 (by omega)]

theorem MatrixCopy.rows_fold (p : MatrixCopy) (original working : Memory) :
    (List.range p.rows).foldl (p.writeRow original) working =
      p.rowVisits.foldl (p.writeWord original) working := by
  have aux (rs : List Nat) (m : Memory) :
      rs.foldl (p.writeRow original) m =
        (rs.flatMap (fun r => (List.range p.cols).map (fun c => (r,c)))).foldl
          (p.writeWord original) m := by
    induction rs generalizing m with
    | nil => rfl
    | cons r rs ih =>
      simp only [List.foldl_cons, List.flatMap_cons, List.foldl_append, List.foldl_map]
      exact ih (p.writeRow original m r)
  exact aux (List.range p.rows) working

end Salty.CByte
