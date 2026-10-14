import Salty.Model.ByteISA
import Salty.Proofs.Core.Behavior
import Salty.Proofs.Core.Memory

/-! A small assembly-like instruction semantics for integer byte-vector programs.
This is an executable intermediate language, not an ISA-validated NEON/RVV subset or a decoder.
No floating-point instruction is accepted. Concrete source/binary lifting is
still required before a program in this syntax can certify a repository kernel.
-/
namespace Salty.ByteISA

theorem loadLanes_length (m : Memory) (base : Address) (n offset : Nat) (bytes : List Byte)
    (h : loadLanes m base n offset = .ok bytes) : bytes.length = n := by
  induction n generalizing offset bytes with
  | zero =>
    simp only [loadLanes, Except.ok.injEq] at h
    subst bytes
    rfl
  | succ n ih =>
    cases he : m.load (base + BitVec.ofNat 64 offset) with
    | none => simp [loadLanes, he] at h
    | some byte =>
      cases ht : loadLanes m base n (offset + 1) with
      | error fault => simp [loadLanes, he, ht, Except.map] at h
      | ok tail =>
        simp only [loadLanes, he, ht, Except.map, Except.ok.injEq] at h
        subst bytes
        simp [ih (offset + 1) tail ht]

/-- A successful vector store preserves every byte outside its addressed lanes,
including when 64-bit address arithmetic wraps. -/
theorem storeLanes_frame (base : Address) (values : Nat → Byte) (n offset : Nat)
    (before after : Memory) (p : Address)
    (outside : ∀ j, offset ≤ j → j < offset + n → p ≠ base + BitVec.ofNat 64 j)
    (h : storeLanes base values n offset before = .ok after) :
    after.data p = before.data p := by
  induction n generalizing offset before after with
  | zero =>
    simp only [storeLanes, Except.ok.injEq] at h
    subst after
    rfl
  | succ n ih =>
    cases hw : before.writable (base + BitVec.ofNat 64 offset) with
    | false => simp [storeLanes, Memory.store, hw] at h
    | true =>
      simp only [storeLanes, Memory.store, hw, ↓reduceIte] at h
      have rest := ih (offset + 1) (before.write (base + BitVec.ofNat 64 offset) (values offset))
        after (by intro j hlo hhi; exact outside j (by omega) (by omega)) h
      rw [rest, Memory.write_other]
      exact outside offset (by omega) (by omega)

/-- The semantics faults on an out-of-range PC, rather than interpreting it
as an implicit successful return. -/
theorem invalidPC_faults (program : List Instruction) (capacity : Nat) (s : State)
    (h : program[s.pc]? = none) :
    (machine program capacity).next s = .inl (.fault ⟨.invalidPC, 0, s.memory.data⟩) := by
  simp [machine, h]

theorem store_zero (base : Address) (values : Nat → Byte) (offset : Nat) (m : Memory) :
    storeLanes base values 0 offset m = .ok m := rfl

end Salty.ByteISA
