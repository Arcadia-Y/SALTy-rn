import Salty.Model.CWordCodec
import Salty.Proofs.Core.CByteMemory

namespace Salty.CByte

theorem bytes32_decode (a b c d : Byte) :
    bytes32 (unsignedWord [a,b,c,d] : Int) = [a,b,c,d] := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  simp only [Nat.reducePow] at ha hb hc hd
  simp only [bytes32, unsignedWord, List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_ofInt, Nat.reducePow, Int.reduceNatCast] <;> omega

theorem unsignedWord_bound (bs : List Byte) (length : bs.length = 4) : unsignedWord bs < 2^32 := by
  rcases bs with _ | ⟨a, bs⟩ <;> simp only [List.length_nil, List.length_cons] at length
  · omega
  rcases bs with _ | ⟨b, bs⟩ <;> simp only [List.length_nil, List.length_cons] at length
  · omega
  rcases bs with _ | ⟨c, bs⟩ <;> simp only [List.length_nil, List.length_cons] at length
  · omega
  rcases bs with _ | ⟨d, bs⟩ <;> simp only [List.length_nil, List.length_cons] at length
  · omega
  have nil : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst bs
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  simp [unsignedWord]
  omega

theorem bytes32_unsignedWord (bs : List Byte) (length : bs.length = 4) : bytes32 (unsignedWord bs : Int) = bs := by
  rcases bs with _ | ⟨a, bs⟩ <;> simp only [List.length_nil, List.length_cons] at length
  · omega
  rcases bs with _ | ⟨b, bs⟩ <;> simp only [List.length_nil, List.length_cons] at length
  · omega
  rcases bs with _ | ⟨c, bs⟩ <;> simp only [List.length_nil, List.length_cons] at length
  · omega
  rcases bs with _ | ⟨d, bs⟩ <;> simp only [List.length_nil, List.length_cons] at length
  · omega
  have nil : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst bs
  exact bytes32_decode a b c d

/-- An actual signed word load followed by C's uint32 conversion recovers all
four original bytes, including values whose sign bit is set. -/
theorem unsigned_load_roundtrip (m : Memory) (a : Address)
    (readable : ∀ p, Footprint a 4 p → m.readable p = true) :
    ∃ n, loadParam m a = some (.integer n) ∧
      bytes32 (convert .u32 n) = readBytes m a 4 ∧ 0 ≤ convert .u32 n ∧ convert .u32 n < 2^32 := by
  let bs := readBytes m a 4
  let word := BitVec.ofNat 32 (unsignedWord bs)
  have len : bs.length = 4 := by simp [bs]
  have bound := unsignedWord_bound bs len
  have reinterpret : convert .u32 word.toInt = (unsignedWord bs : Int) := by
    simp only [convert, BitVec.ofInt_toInt, word, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt bound]
  refine ⟨word.toInt, ?_, ?_, ?_, ?_⟩
  · simp only [loadParam, loadBytes_success m a 4 readable, Option.bind_some]
    rfl
  · rw [reinterpret]
    exact bytes32_unsignedWord bs len
  · rw [reinterpret]; omega
  · rw [reinterpret]; omega

end Salty.CByte
