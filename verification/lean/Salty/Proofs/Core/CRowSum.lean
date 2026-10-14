import Salty.Model.CWordCodec
import Salty.Proofs.Core.CWordCodec

namespace Salty.CByte
open ReductionISA

def rowBytePrim : Interpretation → Prim
  | .signed => .widenAddByte16S
  | .unsigned => .widenAddByte16U

def rowHalfPrim : Interpretation → Prim
  | .signed => .widenAddHalf32S
  | .unsigned => .widenAddHalf32U

def rowByteRVVPrim : Interpretation → Prim
  | .signed => .widenAddByte16RVVS
  | .unsigned => .widenAddByte16RVVU

def rowHalfRVVPrim : Interpretation → Prim
  | .signed => .widenAddHalf32RVVS
  | .unsigned => .widenAddHalf32RVVU


set_option maxHeartbeats 1000000

theorem row_byte_intrinsic (kind : Interpretation) (cfg : Config) (m : Memory)
    (acc : List (BitVec 16)) (xs : List Byte) (ha : acc.length = 8) (hx : xs.length = 8) :
    intrinsic cfg m (rowBytePrim kind) [.halfwords acc, .vector 1 xs] =
      some (.halfwords (WideningISA.widenAdd16 kind acc xs)) := by
  cases kind <;> simp [rowBytePrim, intrinsic, wideningIntrinsic, ha, hx]

theorem row_half_intrinsic (kind : Interpretation) (cfg : Config) (m : Memory)
    (acc : List (BitVec 32)) (xs : List (BitVec 16)) (ha : acc.length = 4) (hx : xs.length = 4) :
    intrinsic cfg m (rowHalfPrim kind) [.words32 acc, .halfwords xs] =
      some (.words32 (WideningISA.widenAdd32 kind acc xs)) := by
  cases kind <;> simp [rowHalfPrim, intrinsic, wideningIntrinsic, ha, hx]

theorem row_byte_rvv_intrinsic (kind : Interpretation) (cfg : Config) (m : Memory) (n : Nat)
    (acc : List (BitVec 16)) (xs : List Byte) (ha : acc.length = n) (hx : xs.length = n) (cap : n ≤ cfg.capacity) :
    intrinsic cfg m (rowByteRVVPrim kind) [.halfwords acc, .vector 1 xs, .integer n] =
      some (.halfwords (WideningISA.widenAdd16 kind acc xs)) := by
  have ta : acc.take n = acc := List.take_of_length_le (by omega)
  have tx : xs.take n = xs := List.take_of_length_le (by omega)
  cases kind <;> simp [rowByteRVVPrim, intrinsic, wideningIntrinsic, ha, hx, cap, ta, tx]

theorem row_half_rvv_intrinsic (kind : Interpretation) (cfg : Config) (m : Memory) (n : Nat)
    (acc : List (BitVec 32)) (xs : List (BitVec 16)) (ha : acc.length = n) (hx : xs.length = n) (cap : n ≤ cfg.capacity) :
    intrinsic cfg m (rowHalfRVVPrim kind) [.words32 acc, .halfwords xs, .integer n] =
      some (.words32 (WideningISA.widenAdd32 kind acc xs)) := by
  have ta : acc.take n = acc := List.take_of_length_le (by omega)
  have tx : xs.take n = xs := List.take_of_length_le (by omega)
  cases kind <;> simp [rowHalfRVVPrim, intrinsic, wideningIntrinsic, ha, hx, cap, ta, tx]

theorem unsignedWord_bytes32 (x : BitVec 32) : unsignedWord (bytes32 (x.toNat : Int)) = x.toNat := by
  have bound := x.isLt
  simp only [unsignedWord, bytes32, List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero,
    BitVec.toNat_ofInt, Nat.reducePow, Int.reduceNatCast]
  omega

theorem decodeWords32_encode (xs : List (BitVec 32)) : decodeWords32 xs.length (encodeWords32 xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have len : (bytes32 (x.toNat : Int)).length = 4 := by simp [bytes32]
    have take : (bytes32 (x.toNat : Int) ++ encodeWords32 xs).take 4 = bytes32 (x.toNat : Int) := by
      simpa only [len] using List.take_left (l₁ := bytes32 (x.toNat : Int)) (l₂ := encodeWords32 xs)
    have drop : (bytes32 (x.toNat : Int) ++ encodeWords32 xs).drop 4 = encodeWords32 xs := by
      simpa only [len] using List.drop_left (l₁ := bytes32 (x.toNat : Int)) (l₂ := encodeWords32 xs)
    change BitVec.ofNat 32 (unsignedWord ((bytes32 (x.toNat : Int) ++ encodeWords32 xs).take 4)) ::
      decodeWords32 xs.length ((bytes32 (x.toNat : Int) ++ encodeWords32 xs).drop 4) = x::xs
    rw [take, drop, unsignedWord_bytes32, ih]
    simp

@[simp] theorem encodeWords32_length (xs : List (BitVec 32)) : (encodeWords32 xs).length = 4*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (bytes32 (x.toNat : Int) ++ encodeWords32 xs).length = _
    simp [bytes32, ih]
    omega

@[simp] theorem readWords32_length (m : Memory) (a : Address) (n : Nat) :
    (readWords32 m a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [readWords32, ih]

theorem decodeWords32_read (m : Memory) (a : Address) (n : Nat) :
    decodeWords32 n (readBytes m a (4*n)) = readWords32 m a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have count : 4*(n+1) = 4+4*n := by omega
    rw [count, readBytes_add]
    simp only [decodeWords32, readBytes_length, List.take_left', List.drop_left', readWords32]
    change readWord32 m a :: decodeWords32 n (readBytes m (a+4) (4*n)) = _
    rw [ih]

theorem bytes32_readWord (m : Memory) (a : Address) :
    bytes32 ((readWord32 m a).toNat : Int) = readBytes m a 4 := by
  have bound := unsignedWord_bound (readBytes m a 4) (readBytes_length m a 4)
  simp only [readWord32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  exact bytes32_unsignedWord _ (readBytes_length m a 4)

/-- Reading and re-encoding a vector preserves its exact bytes. -/
theorem encodeWords32_read (m : Memory) (a : Address) (n : Nat) :
    encodeWords32 (readWords32 m a n) = readBytes m a (4*n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    change bytes32 ((readWord32 m a).toNat : Int) ++ encodeWords32 (readWords32 m (a+4) n) = _
    rw [bytes32_readWord, ih]
    have count : 4*(n+1) = 4+4*n := by omega
    rw [count, readBytes_add]
    rfl

end Salty.CByte
