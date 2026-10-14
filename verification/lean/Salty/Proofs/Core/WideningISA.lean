import Salty.Model.WideningISA
import Salty.Proofs.Core.ReductionISA

/-! Lane semantics for the signed and unsigned row-sum development. NEON
SADDW/UADDW and RVV vwadd.wv/vwaddu.wv add one widened input per lane.
These facts do not claim whole-kernel correspondence or equivalence.
Primary references: https://arm-software.github.io/acle/neon_intrinsics/advsimd.html
and https://docs.riscv.org/reference/isa/v20260120/unpriv/v-st-ext.html §30.1.11.2. -/
namespace Salty.WideningISA
open ReductionISA

/-- Each lane contains k row values, including any substituted zero rows. -/
def LaneBound (kind : Interpretation) (k : Nat) (acc : BitVec 16) : Prop :=
  match kind with
  | .signed => -128*(k : Int) ≤ acc.toInt ∧ acc.toInt ≤ 127*(k : Int)
  | .unsigned => (acc.toNat : Int) ≤ 255*(k : Int)
open ReductionISA

theorem laneBound_zero (kind : Interpretation) : LaneBound kind 0 0 := by
  cases kind <;> simp [LaneBound]

theorem addByte16_eq_ofInt (kind : Interpretation) (acc : BitVec 16) (x : BitVec 8) :
    addByte16 kind acc x = BitVec.ofInt 16 (value kind acc+value kind x) := by
  cases kind <;> simp [addByte16, value, BitVec.ofInt_add]

/-- A full 256-byte sum fits 16 bits in either interpretation. The kernels use
252 rows, the largest multiple of seven below this limit. -/
theorem addByte16_exact (kind : Interpretation) (k : Nat) (small : k < 256)
    (acc : BitVec 16) (x : BitVec 8) (bound : LaneBound kind k acc) :
    value kind (addByte16 kind acc x) = value kind acc+value kind x := by
  have bx := byte_bounds kind x
  rw [addByte16_eq_ofInt]
  cases kind with
  | signed =>
    simp only [LaneBound, value] at *
    apply BitVec.toInt_ofInt_eq_self (by decide) <;> omega
  | unsigned =>
    simp only [LaneBound, value] at *
    have lo : 0 ≤ (acc.toNat : Int)+x.toNat := by omega
    have hi : (acc.toNat : Int)+x.toNat < 65536 := by omega
    rw [BitVec.toNat_ofInt]
    change ((((acc.toNat : Int)+x.toNat)%65536).toNat : Int) = _
    rw [Int.emod_eq_of_lt lo hi, Int.toNat_of_nonneg lo]

theorem addByte16_bound (kind : Interpretation) (k : Nat) (small : k < 256)
    (acc : BitVec 16) (x : BitVec 8) (bound : LaneBound kind k acc) :
    LaneBound kind (k+1) (addByte16 kind acc x) := by
  have exact := addByte16_exact kind k small acc x bound
  have bx := byte_bounds kind x
  cases kind <;> simp only [LaneBound, value] at * <;> omega

/-- Sequential wide adds have the exact mathematical row sum throughout one
bounded halfword batch, rather than merely a modular relation. -/
theorem fold_exact (kind : Interpretation) (xs : List (BitVec 8)) (k : Nat) (acc : BitVec 16)
    (small : k+xs.length ≤ 256) (bound : LaneBound kind k acc) :
    value kind (xs.foldl (addByte16 kind) acc) = value kind acc+sumInts (xs.map (value kind)) ∧
      LaneBound kind (k+xs.length) (xs.foldl (addByte16 kind) acc) := by
  induction xs generalizing k acc with
  | nil => constructor
           · simp [sumInts]
           · simpa using bound
  | cons x xs ih =>
    have stepSmall : k < 256 := by simp only [List.length_cons] at small; omega
    have exact := addByte16_exact kind k stepSmall acc x bound
    have next := addByte16_bound kind k stepSmall acc x bound
    have rest := ih (k+1) (addByte16 kind acc x) (by simp only [List.length_cons] at small; omega) next
    constructor
    · simpa [List.foldl, sumInts, exact, Int.add_assoc] using rest.1
    · simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest.2

theorem widen_batch (kind : Interpretation) (xs : List (BitVec 8)) (acc : BitVec 32)
    (small : xs.length ≤ 256) :
    addHalf32 kind acc (xs.foldl (addByte16 kind) 0) = acc+sumWords (widen32 kind xs) := by
  have exact := (fold_exact kind xs 0 0 (by omega) (laneBound_zero kind)).1
  have zero : value kind (0 : BitVec 16) = 0 := by cases kind <;> rfl
  rw [zero, Int.zero_add] at exact
  unfold addHalf32
  rw [exact]
  congr 1
  simpa only [widen32, List.map_map, Function.comp_def] using (sumWords_ofInt (xs.map (value kind))).symm

theorem widenAdd16_length (kind : Interpretation) (acc : List (BitVec 16)) (xs : List (BitVec 8))
    (length : acc.length = xs.length) : (widenAdd16 kind acc xs).length = acc.length := by
  simp [widenAdd16, List.length_zipWith, length]

theorem widenAdd32_length (kind : Interpretation) (acc : List (BitVec 32)) (xs : List (BitVec 16))
    (length : acc.length = xs.length) : (widenAdd32 kind acc xs).length = acc.length := by
  simp [widenAdd32, List.length_zipWith, length]

end Salty.WideningISA
