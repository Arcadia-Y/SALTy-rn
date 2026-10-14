import Salty.Model.CWordMemory
import Salty.Proofs.Core.CByteMemory

/-! Byte-accurate strided 32-bit stores for the transpose/packing developments.
These lemmas concern actual permission checks and byte-address arithmetic;
they are supporting results, not whole-kernel equivalence theorems. -/
set_option maxHeartbeats 1000000
namespace Salty.CByte

private theorem stride_succ (a stride : Address) (i : Nat) :
    a + stride * BitVec.ofNat 64 (i + 1) = a + stride + stride * BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_add, BitVec.mul_add]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.mul_one]
  ac_rfl

theorem stridedFootprint_succ (a stride p : Address) (n : Nat) :
    StridedFootprint a stride (n + 1) p ↔
      Footprint a 4 p ∨ StridedFootprint (a + stride) stride n p := by
  constructor
  · rintro ⟨i, hi, hp⟩
    cases i with
    | zero => exact Or.inl (by simpa using hp)
    | succ i => exact Or.inr ⟨i, by omega, by simpa only [stride_succ] using hp⟩
  · rintro (hp | ⟨i, hi, hp⟩)
    · exact ⟨0, by omega, by simpa using hp⟩
    · exact ⟨i + 1, by omega, by simpa only [stride_succ] using hp⟩

@[simp] theorem writeStrided32_readable (m : Memory) (a stride : Address)
    (bs : List Byte) (n : Nat) : (writeStrided32 m a stride bs n).readable = m.readable := by
  induction n generalizing m a bs with
  | zero => rfl
  | succ n ih => simp [writeStrided32, ih]

@[simp] theorem writeStrided32_writable (m : Memory) (a stride : Address)
    (bs : List Byte) (n : Nat) : (writeStrided32 m a stride bs n).writable = m.writable := by
  induction n generalizing m a bs with
  | zero => rfl
  | succ n ih => simp [writeStrided32, ih]

theorem storeStrided32_success (m : Memory) (a stride : Address) (bs : List Byte) (n : Nat)
    (length : 4 * n ≤ bs.length)
    (safe : ∀ p, StridedFootprint a stride n p → m.writable p = true) :
    storeStrided32 m a stride bs n = some (writeStrided32 m a stride bs n) := by
  induction n generalizing m a bs with
  | zero => rfl
  | succ n ih =>
    have ht : (bs.take 4).length = 4 := by simp; omega
    have hs : storeBytes m a (bs.take 4) = some (writeBytes m a (bs.take 4)) := by
      apply storeBytes_success
      intro p hp
      apply safe p
      apply (stridedFootprint_succ a stride p n).mpr
      exact Or.inl (by simpa only [ht] using hp)
    simp only [storeStrided32, hs, Option.bind_some, writeStrided32]
    apply ih
    · simp only [List.length_drop]; omega
    · intro p hp
      simpa using safe p ((stridedFootprint_succ a stride p n).mpr (Or.inr hp))

theorem writeStrided32_frame (m : Memory) (a stride p : Address) (bs : List Byte) (n : Nat)
    (outside : ¬ StridedFootprint a stride n p) :
    (writeStrided32 m a stride bs n).data p = m.data p := by
  induction n generalizing m a bs with
  | zero => rfl
  | succ n ih =>
    have h := mt (stridedFootprint_succ a stride p n).mpr outside
    simp only [not_or] at h
    rw [writeStrided32, ih _ _ _ h.2]
    apply writeBytes_frame
    intro hp
    apply h.1
    exact footprint_mono (by simp only [List.length_take]; omega) hp

/-- The two zipped vectors contain rows transposed at 32-bit granularity,
without reinterpreting or rounding their contents. -/
theorem zipU32x2_blocks (cfg : Config) (m : Memory) (a b c d : List Byte)
    (ha : a.length = 4) (hb : b.length = 4) (hc : c.length = 4) (hd : d.length = 4) :
    intrinsic cfg m .zipU32x2 [.vector 4 (a ++ b), .vector 4 (c ++ d)] =
      some (.vectors 4 [a ++ c, b ++ d]) := by
  simp only [intrinsic, List.length_append, ha, hb, hc, hd]
  simp only [Nat.reduceAdd, and_self, ↓reduceIte, List.take_left' ha, List.take_left' hc,
    List.drop_left' ha, List.drop_left' hc]

theorem readBytes_writeStrided32_disjoint (m : Memory) (input output stride : Address)
    (bs : List Byte) (count lanes : Nat)
    (disjoint : ∀ p, Footprint input count p → ¬ StridedFootprint output stride lanes p) :
    readBytes (writeStrided32 m output stride bs lanes) input count = readBytes m input count := by
  induction count generalizing input with
  | zero => rfl
  | succ count ih =>
    rw [readBytes, readBytes, writeStrided32_frame _ _ _ _ _ _
      (disjoint input ((footprint_succ _ _ _).mpr (Or.inl rfl)))]
    rw [ih (input + 1) (fun p hp => disjoint p ((footprint_succ _ _ _).mpr (Or.inr hp)))]

private theorem memory_ext {a b : Memory} (data : a.data = b.data)
    (readable : a.readable = b.readable) (writable : a.writable = b.writable) : a = b := by
  cases a
  cases b
  cases data
  cases readable
  cases writable
  rfl

private theorem write_comm (m : Memory) (a b : Address) (x y : Byte) (hne : a ≠ b) :
    (m.write a x).write b y = (m.write b y).write a x := by
  apply memory_ext
  · funext p
    by_cases ha : p = a <;> by_cases hb : p = b <;> simp_all [Memory.write]
  · rfl
  · rfl

theorem writeBytes_write_comm (m : Memory) (a p : Address) (bs : List Byte) (value : Byte)
    (outside : ¬ Footprint a bs.length p) :
    writeBytes (m.write p value) a bs = (writeBytes m a bs).write p value := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    have h := mt (footprint_succ a p bs.length).mpr outside
    simp only [not_or] at h
    simp only [writeBytes]
    rw [write_comm m p a value b h.1]
    exact ih (m.write a b) (a + 1) h.2

/-- Disjoint byte blocks commute even when their instruction schedules differ.
The separation premise concerns actual byte addresses, including wrap. -/
theorem writeBytes_comm (m : Memory) (a b : Address) (xs ys : List Byte)
    (separate : ∀ p, Footprint a xs.length p → ¬ Footprint b ys.length p) :
    writeBytes (writeBytes m a xs) b ys = writeBytes (writeBytes m b ys) a xs := by
  induction xs generalizing m a with
  | nil => rfl
  | cons x xs ih =>
    have head : ¬ Footprint b ys.length a :=
      separate a ((footprint_succ a a xs.length).mpr (Or.inl rfl))
    have tail : ∀ p, Footprint (a + 1) xs.length p → ¬ Footprint b ys.length p :=
      fun p hp => separate p ((footprint_succ a p xs.length).mpr (Or.inr hp))
    simp only [writeBytes]
    rw [ih (m.write a x) (a + 1) tail]
    rw [writeBytes_write_comm m b a ys x head]

/-- The executable stride guard excludes every pair of overlapping active lane
footprints. Thus the chosen increasing-lane store order has no semantic effect
on defined accesses covered by the source bridge. -/
theorem DisjointStride32.lanes {stride a p : Address} {lanes i j : Nat}
    (layout : DisjointStride32 stride lanes) (hi : i < lanes) (hj : j < lanes) (hne : i ≠ j)
    (left : Footprint (a + stride * BitVec.ofNat 64 i) 4 p) :
    ¬ Footprint (a + stride * BitVec.ofNat 64 j) 4 p := by
  intro right
  rcases layout with small | ⟨width, extent⟩
  · omega
  obtain ⟨b, hb, hpb⟩ := left
  obtain ⟨c, hc, hpc⟩ := right
  have bound (r t : Nat) (hr : r < lanes) (ht : t < 4) :
      stride.toNat * r + t < 2^64 := by
    have hm := Nat.mul_le_mul_left stride.toNat (show r ≤ lanes - 1 by omega)
    omega
  have hbnd := bound i b hi hb
  have hcnd := bound j c hj hc
  have reshape (r t : Nat) :
      a + stride * BitVec.ofNat 64 r + BitVec.ofNat 64 t =
      a + BitVec.ofNat 64 (stride.toNat * r + t) := by
    simp only [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_assoc]
  have he := hpb.symm.trans hpc
  rw [reshape i b, reshape j c] at he
  have hn := congrArg BitVec.toNat ((BitVec.add_right_inj a).mp he)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbnd, Nat.mod_eq_of_lt hcnd] at hn
  by_cases hij : i < j
  · have hm := Nat.mul_le_mul_left stride.toNat (show i + 1 ≤ j by omega)
    simp only [Nat.mul_add, Nat.mul_one] at hm
    omega
  · have hm := Nat.mul_le_mul_left stride.toNat (show j + 1 ≤ i by omega)
    simp only [Nat.mul_add, Nat.mul_one] at hm
    omega

theorem strided_lane_order_independent (m : Memory) (a stride : Address) (bs : List Byte)
    (lanes : Nat) (left right : List Nat) (layout : DisjointStride32 stride lanes)
    (permutation : left.Perm right) (valid : ∀ i ∈ left, i < lanes) :
    left.foldl (fun mem lane => writeLane32 mem a stride bs lane) m =
      right.foldl (fun mem lane => writeLane32 mem a stride bs lane) m := by
  apply permutation.foldl_eq'
  intro i hi j hj mem
  by_cases h : i = j
  · subst j; rfl
  · apply writeBytes_comm
    intro p hp hq
    apply layout.lanes (valid i hi) (valid j hj) h
    · exact footprint_mono (by simp only [List.length_take]; omega) hp
    · exact footprint_mono (by simp only [List.length_take]; omega) hq

private theorem writeStrided32_range' (m : Memory) (a stride : Address) (bs : List Byte)
    (start n : Nat) :
    writeStrided32 m (a + stride * BitVec.ofNat 64 start) stride (bs.drop (4 * start)) n =
      (List.range' start n).foldl (fun mem lane => writeLane32 mem a stride bs lane) m := by
  induction n generalizing m start with
  | zero => simp [writeStrided32]
  | succ n ih =>
    simp only [writeStrided32, List.range'_succ, List.foldl_cons]
    have ha : a + stride * BitVec.ofNat 64 start + stride =
        a + stride * BitVec.ofNat 64 (start + 1) := by
      rw [stride_succ]
      ac_rfl
    have hd : (bs.drop (4 * start)).drop 4 = bs.drop (4 * (start + 1)) := by
      simp [List.drop_drop, Nat.mul_add, Nat.add_comm]
    rw [ha, hd, ih]
    rfl

theorem writeStrided32_lane_order (m : Memory) (a stride : Address) (bs : List Byte) (lanes : Nat) :
    writeStrided32 m a stride bs lanes =
      (List.range lanes).foldl (fun mem lane => writeLane32 mem a stride bs lane) m := by
  simpa [List.range_eq_range'] using writeStrided32_range' m a stride bs 0 lanes

/-- The actual sequential primitive's successful result agrees with every
permutation of active lane stores admitted by the architecture. -/
theorem storeStrided32_any_order (m : Memory) (a stride : Address) (bs : List Byte) (lanes : Nat)
    (layout : DisjointStride32 stride lanes) (length : 4 * lanes ≤ bs.length)
    (safe : ∀ p, StridedFootprint a stride lanes p → m.writable p = true)
    (order : List Nat) (permutation : (List.range lanes).Perm order) :
    storeStrided32 m a stride bs lanes =
      some (order.foldl (fun mem lane => writeLane32 mem a stride bs lane) m) := by
  rw [storeStrided32_success m a stride bs lanes length safe, writeStrided32_lane_order]
  rw [strided_lane_order_independent m a stride bs lanes (List.range lanes) order layout
    permutation (by intro i hi; simpa using hi)]

private theorem write_overwrite (m : Memory) (a : Address) (x y : Byte) :
    (m.write a x).write a y = m.write a y := by
  apply memory_ext
  · funext p
    by_cases h : p = a <;> simp [Memory.write, h]
  · rfl
  · rfl

theorem writeBytes_erase_write (m : Memory) (a p : Address) (bs : List Byte) (value : Byte)
    (inside : Footprint a bs.length p) :
    writeBytes (m.write p value) a bs = writeBytes m a bs := by
  induction bs generalizing m a with
  | nil => obtain ⟨i, hi, _⟩ := inside; simp at hi
  | cons b bs ih =>
    by_cases same : p = a
    · subst p
      simp only [writeBytes, write_overwrite]
    · have tail : Footprint (a + 1) bs.length p := by
        have h := (footprint_succ a p bs.length).mp inside
        exact h.resolve_left same
      simp only [writeBytes]
      rw [write_comm m p a value b same]
      exact ih (m.write a b) (a + 1) tail

/-- A later block erases earlier writes whose complete footprint it covers.
This includes intentional aliasing in NEON's odd-column transpose path. -/
theorem writeBytes_erase_block (m : Memory) (oldBase newBase : Address) (old new : List Byte)
    (covers : ∀ p, Footprint oldBase old.length p → Footprint newBase new.length p) :
    writeBytes (writeBytes m oldBase old) newBase new = writeBytes m newBase new := by
  induction old generalizing m oldBase with
  | nil => rfl
  | cons b bs ih =>
    have head : Footprint newBase new.length oldBase :=
      covers oldBase ((footprint_succ _ _ _).mpr (Or.inl rfl))
    have tail : ∀ p, Footprint (oldBase + 1) bs.length p → Footprint newBase new.length p :=
      fun p hp => covers p ((footprint_succ _ _ _).mpr (Or.inr hp))
    rw [writeBytes, ih (m.write oldBase b) (oldBase + 1) tail]
    exact writeBytes_erase_write m newBase oldBase new b head

theorem writeBytes_overwrite (m : Memory) (a : Address) (old new : List Byte)
    (length : old.length ≤ new.length) :
    writeBytes (writeBytes m a old) a new = writeBytes m a new :=
  writeBytes_erase_block m a a old new (fun _ hp => footprint_mono length hp)

theorem readBytes_slice (m : Memory) (a : Address) (start count width : Nat)
    (bounds : start + width ≤ count) :
    ((readBytes m a count).drop start).take width =
      readBytes m (a + BitVec.ofNat 64 start) width := by
  have hs : start ≤ count := by omega
  have split : count = start + (count - start) := by omega
  rw [split, readBytes_add]
  have hd : (readBytes m a start ++
      readBytes m (a + BitVec.ofNat 64 start) (count - start)).drop start =
      readBytes m (a + BitVec.ofNat 64 start) (count - start) := by
    exact List.drop_left' (readBytes_length ..)
  rw [hd]
  exact readBytes_take m (a + BitVec.ofNat 64 start) width (count - start) (by omega)

end Salty.CByte
