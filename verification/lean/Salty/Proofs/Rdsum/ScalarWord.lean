import Salty.Proofs.Rdsum.WordMemory

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- Byte encoding depends only on the low 32 bits, including for negative integers. -/
theorem bytes32_word_congr (a b : Int) (h : BitVec.ofInt 32 a = BitVec.ofInt 32 b) :
    bytes32 a = bytes32 b := by
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofInt, Nat.reducePow, Int.reduceNatCast] at hn
  simp only [bytes32, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_ofInt, Nat.reducePow, Int.reduceNatCast] <;> omega

theorem bytes32_signed_add (a b : BitVec 32) :
    bytes32 (a.toInt+b.toInt) = bytes32 ((a+b).toNat : Int) := by
  apply bytes32_word_congr
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem bytes32_unsigned_add (a b : BitVec 32) :
    bytes32 (convert .u32 ((a.toNat : Int)+(b.toNat : Int))) = bytes32 ((a+b).toNat : Int) := by
  apply bytes32_word_congr
  simp [convert, BitVec.ofInt_add, BitVec.ofNat_add]

theorem loadParam_readWord (m : Memory) (a : Address)
    (readable : ∀ p, Footprint a 4 p → m.readable p = true) :
    loadParam m a = some (.integer (readWord32 m a).toInt) := by
  simp only [loadParam, loadBytes_success m a 4 readable, Option.bind_some]
  rfl

theorem convert_word_unsigned (x : BitVec 32) : convert .u32 x.toInt = (x.toNat : Int) := by
  simp [convert]

end Salty.Kernels.Rdsum
