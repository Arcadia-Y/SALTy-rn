import Salty.Proofs.Rdsum.NeonLastStores

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

theorem list_four {α : Type} (xs : List α) (len : xs.length = 4) :
    ∃ a b c d, xs = [a,b,c,d] := by
  obtain ⟨a,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < xs.length)
  simp only [List.length_cons] at len
  obtain ⟨b,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < xs.length)
  simp only [List.length_cons] at len
  obtain ⟨c,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < xs.length)
  simp only [List.length_cons] at len
  obtain ⟨d,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < xs.length)
  have nil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using len)
  subst xs
  exact ⟨a,b,c,d,rfl⟩

theorem afterTwo_read_next (s : State) (output : Address) (acc : List (BitVec 32)) (len : acc.length = 4) :
    readWord32 (afterTwo s output acc).memory (output+8) = readWord32 s.memory (output+8) := by
  have frame := readWord32_after_prefix s.memory output 2
    (encodeWords32 (storedWords s.memory output 2 (acc.take 2))) (by simp [len]) (by decide)
  exact frame

/-- The only scalar addition is the final original word of an odd-sized suffix. -/
def LastOriginalDefined (kind : Interpretation) (m : Memory) (output : Address)
    (acc : List (BitVec 32)) (n : Nat) : Prop :=
  n % 2 = 1 → ScalarStoreDefined kind
    (readWord32 m (output+BitVec.ofNat 64 (4*(n-1)))) acc[n-1]!

theorem last_defined_original (kind : Interpretation) (s : State) (output : Address)
    (acc : List (BitVec 32)) (len : acc.length = 4) (n : Nat) (small : n < 4)
    (defined : LastOriginalDefined kind s.memory output acc n) :
    LastStoreDefined kind s output acc n := by
  obtain ⟨a,b,c,d,rfl⟩ := list_four acc len
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · trivial
  · simpa [LastOriginalDefined, LastStoreDefined] using defined
  · trivial
  · have h := defined rfl
    change ScalarStoreDefined kind (readWord32 (afterTwo s output [a,b,c,d]).memory (output+8)) _
    rw [afterTwo_read_next s output [a,b,c,d] rfl]
    simpa [rotateWords2] using h

/-- Complete memory result of the actual 2/1 suffix, relative to its original memory. -/
theorem lastStored_memory (s : State) (output : Address) (acc : List (BitVec 32))
    (len : acc.length = 4) (n : Nat) (small : n < 4) :
    (lastStored s output acc n).memory =
      writeBytes s.memory output (encodeWords32 (storedWords s.memory output n (acc.take n))) := by
  obtain ⟨a,b,c,d,rfl⟩ := list_four acc len
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · rfl
  · simp [lastStored, neonScalarStored, update, storedWords, readWords32, encodeWords32]
  · rfl
  · have join := storedWords_write_join_after s.memory output [a,b] [c] (by simp)
    simpa [lastStored, neonScalarStored, afterTwo, neonSmallStored, update, rotateWords2,
      storedWords, readWords32, encodeWords32] using join

@[simp] theorem lastStored_channels (s : State) (output : Address) (acc : List (BitVec 32)) (n : Nat) :
    (lastStored s output acc n).locals "channels" = some (.integer 0) := by
  simp [lastStored, update]

end Salty.Kernels.Rdsum
