import Salty.Model.CByteMemory
import Salty.Proofs.Core.CByte

namespace Salty.CByte

@[simp] theorem writeBytes_readable (m : Memory) (a : Address) (bs : List Byte) :
    (writeBytes m a bs).readable = m.readable := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih => simp [writeBytes, ih, Memory.write]

@[simp] theorem writeBytes_writable (m : Memory) (a : Address) (bs : List Byte) :
    (writeBytes m a bs).writable = m.writable := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih => simp [writeBytes, ih, Memory.write]

private theorem address_succ (a : Address) (i : Nat) :
    a + BitVec.ofNat 64 (i + 1) = a + 1 + BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_add]
  change a + (BitVec.ofNat 64 i + 1) = a + 1 + BitVec.ofNat 64 i
  ac_rfl

theorem footprint_succ (a p : Address) (n : Nat) :
    Footprint a (n + 1) p ↔ p = a ∨ Footprint (a + 1) n p := by
  constructor
  · rintro ⟨i, hi, hp⟩
    cases i with
    | zero => exact Or.inl (by simpa using hp)
    | succ i => exact Or.inr ⟨i, by omega, hp.trans (address_succ a i)⟩
  · rintro (rfl | ⟨i, hi, hp⟩)
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨i + 1, by omega, hp.trans (address_succ a i).symm⟩

theorem writeBytes_frame (m : Memory) (a p : Address) (bs : List Byte)
    (outside : ¬ Footprint a bs.length p) : (writeBytes m a bs).data p = m.data p := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    have h := mt (footprint_succ a p bs.length).mpr outside
    simp only [not_or] at h
    rw [writeBytes, ih _ _ h.2, Memory.write_other _ _ _ _ h.1]

/-- If stores succeed, their result is precisely the total functional write.
This lemma does not assume success for forbidden addresses. -/
theorem storeBytes_result {m result : Memory} {a : Address} {bs : List Byte}
    (h : storeBytes m a bs = some result) : result = writeBytes m a bs := by
  induction bs generalizing m a with
  | nil => simpa [storeBytes, writeBytes] using h.symm
  | cons b bs ih =>
    simp only [storeBytes, bind, Option.bind_eq_some_iff] at h
    obtain ⟨m', hm, hrest⟩ := h
    simp only [Memory.store] at hm
    split at hm
    · cases hm
      exact ih hrest
    · contradiction

/-- Stores terminate successfully when their complete footprint is writable. -/
theorem storeBytes_success (m : Memory) (a : Address) (bs : List Byte)
    (safe : ∀ p, Footprint a bs.length p → m.writable p = true) :
    storeBytes m a bs = some (writeBytes m a bs) := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    have head : m.writable a = true := safe a ((footprint_succ _ _ _).mpr (Or.inl rfl))
    simp only [storeBytes, Memory.store, head, ↓reduceIte, Option.bind_some]
    apply ih
    intro p hp
    exact safe p ((footprint_succ _ _ _).mpr (Or.inr hp))

/-- Reading from any memory with the same permissions/data on the footprint
returns the same bytes. This supports input/output separation without silently
replacing pointer operations by list slicing. -/
theorem loadBytes_congr (m other : Memory) (a : Address) (n : Nat)
    (same : ∀ p, Footprint a n p → m.load p = other.load p) :
    loadBytes m a n = loadBytes other a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have head := same a ((footprint_succ _ _ _).mpr (Or.inl rfl))
    have tail := ih (a + 1) (fun p hp => same p ((footprint_succ _ _ _).mpr (Or.inr hp)))
    simp only [loadBytes, head, tail]

/-- Writes to a disjoint output region preserve input loads, including padded
NEON loads. Disjointness must cover the actual read footprint. -/
theorem loadBytes_writeBytes_disjoint (m : Memory) (input output : Address)
    (n : Nat) (bs : List Byte)
    (disjoint : ∀ p, Footprint input n p → ¬ Footprint output bs.length p) :
    loadBytes (writeBytes m output bs) input n = loadBytes m input n := by
  apply loadBytes_congr
  intro p hp
  simp only [Memory.load, writeBytes_readable, writeBytes_frame _ _ _ _ (disjoint p hp)]

theorem writeBytes_append (m : Memory) (a : Address) (xs ys : List Byte) :
    writeBytes m a (xs ++ ys) =
      writeBytes (writeBytes m a xs) (a + BitVec.ofNat 64 xs.length) ys := by
  induction xs generalizing m a with
  | nil => simp [writeBytes]
  | cons x xs ih => simpa only [List.cons_append, writeBytes, List.length_cons, address_succ] using (ih (m.write a x) (a + 1))

theorem readBytes_congr (m other : Memory) (a : Address) (n : Nat)
    (same : ∀ p, Footprint a n p → m.data p = other.data p) :
    readBytes m a n = readBytes other a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [readBytes, readBytes, same a ((footprint_succ _ _ _).mpr (Or.inl rfl))]
    rw [ih (a + 1) (fun p hp => same p ((footprint_succ _ _ _).mpr (Or.inr hp)))]

theorem footprint_shift_within {a p : Address} {start count total : Nat}
    (bound : start + count ≤ total)
    (hp : Footprint (a + BitVec.ofNat 64 start) count p) : Footprint a total p := by
  obtain ⟨i, hi, he⟩ := hp
  refine ⟨start + i, by omega, ?_⟩
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

@[simp] theorem readBytes_length (m : Memory) (a : Address) (n : Nat) :
    (readBytes m a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [readBytes, ih]

theorem loadBytes_success (m : Memory) (a : Address) (n : Nat)
    (safe : ∀ p, Footprint a n p → m.readable p = true) :
    loadBytes m a n = some (readBytes m a n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have head := safe a ((footprint_succ _ _ _).mpr (Or.inl rfl))
    have tail := ih (a + 1) (fun p hp => safe p ((footprint_succ _ _ _).mpr (Or.inr hp)))
    simp only [loadBytes, Memory.load, head, ↓reduceIte, Option.bind_some, tail, readBytes]
    rfl

theorem readBytes_add (m : Memory) (a : Address) (n k : Nat) :
    readBytes m a (n + k) = readBytes m a n ++ readBytes m (a + BitVec.ofNat 64 n) k := by
  induction n generalizing a with
  | zero => simp [readBytes]
  | succ n ih =>
    rw [Nat.succ_add, readBytes, ih, readBytes, List.cons_append]
    congr 2
    exact congrArg (fun p => readBytes m p k) (address_succ a n).symm

theorem readBytes_take (m : Memory) (a : Address) (n k : Nat) (h : n ≤ k) :
    (readBytes m a k).take n = readBytes m a n := by
  have hk : k = n + (k - n) := by omega
  rw [hk, readBytes_add]
  simp

theorem footprint_mono {a p : Address} {n k : Nat} (h : n ≤ k)
    (hp : Footprint a n p) : Footprint a k p := by
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨i, by omega, rfl⟩

theorem footprint_shift (a p : Address) (n k : Nat)
    (hp : Footprint (a + BitVec.ofNat 64 k) n p) : Footprint a (k + n) p := by
  obtain ⟨i, hi, rfl⟩ := hp
  refine ⟨k + i, by omega, ?_⟩
  simp only [BitVec.ofNat_add, BitVec.add_assoc]

theorem footprint_append (a p : Address) (n k : Nat) :
    Footprint a (n+k) p ↔ Footprint a n p ∨ Footprint (a + BitVec.ofNat 64 n) k p := by
  constructor
  · rintro ⟨i, hi, he⟩
    by_cases left : i < n
    · exact Or.inl ⟨i, left, he⟩
    · right
      refine ⟨i-n, by omega, ?_⟩
      have split : n+(i-n) = i := by omega
      simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, split] using he
  · rintro (hp | hp)
    · exact footprint_mono (by omega) hp
    · exact footprint_shift a p k n hp

theorem readBytes_writeBytes_disjoint (m : Memory) (input output : Address)
    (n : Nat) (bs : List Byte)
    (disjoint : ∀ p, Footprint input n p → ¬ Footprint output bs.length p) :
    readBytes (writeBytes m output bs) input n = readBytes m input n := by
  induction n generalizing input with
  | zero => rfl
  | succ n ih =>
    rw [readBytes, readBytes, writeBytes_frame _ _ _ _
      (disjoint input ((footprint_succ _ _ _).mpr (Or.inl rfl)))]
    rw [ih (input + 1) (fun p hp => disjoint p ((footprint_succ _ _ _).mpr (Or.inr hp)))]

end Salty.CByte
