import Salty.Proofs.QS8Add.Rvv

namespace Salty.Kernels.QS8Add
open CByte

def rvvShiftByteExpr : Expr := .cast .u32 (.bin .band
  (.cast .u32 (.bin .sub (.lit 0) (.cast .u32 (.param (.var "params") 16)))) (.lit 255))
def rvvShiftCountExpr : Expr := .checkedSigned32 (.bin .sub (.cast .i32 (.var "shift_byte"))
  (.conditional (.bin .ge (.var "shift_byte") (.lit 128)) (.lit 256) (.lit 0)))

theorem rvv_shift_byte_eval (cfg : Config) (s : State) (param : Address) (raw : BitVec 32)
    (ptr : s.locals "params" = some (.pointer param))
    (load : loadParam s.memory (param+16#64) = some (.integer raw.toInt)) :
    eval cfg s rvvShiftByteExpr = some (.integer (((-raw).toNat % 256 : Nat) : Int)) := by
  have cast : convert .u32 raw.toInt = raw.toNat := by simp [convert]
  have neg : convert .u32 (-(raw.toNat : Int)) = (-raw).toNat := by
    simp [convert, BitVec.ofInt_neg]
  have mask : (-raw).toNat &&& 255 = (-raw).toNat % 256 :=
    Nat.and_two_pow_sub_one_eq_mod (-raw).toNat 8
  have low : (-raw).toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have castlow : convert .u32 (((-raw).toNat % 256 : Nat) : Int) = ((-raw).toNat % 256 : Nat) := by
    simp only [convert, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (-raw).toNat % 256 < 2^32 by omega)]
  simp only [rvvShiftByteExpr, eval, binary, ptr, load, cast, neg, mask, castlow,
    Option.bind_eq_bind, Option.pure_def, Option.bind_some, Int.zero_sub, Int.toNat_natCast,
    show ¬ ((-raw).toNat : Int) < 0 from by omega,
    show ¬ (255 : Int) < 0 from by decide, or_self, if_false,
    Int.toNat_natCast, show (255 : Int).toNat = 255 from rfl]

theorem cast_i32_low (low : Nat) (bound : low < 256) : convert .i32 (low : Int) = low := by
  change (BitVec.ofNat 32 low).toInt = (low : Int)
  have small : low < 2^32 := by omega
  rw [BitVec.toInt_eq_toNat_of_lt (by simp [Nat.mod_eq_of_lt small]; omega)]
  simp [Nat.mod_eq_of_lt small]

def rvvShiftCountBody : Expr := .bin .sub (.cast .i32 (.var "shift_byte"))
  (.conditional (.bin .ge (.var "shift_byte") (.lit 128)) (.lit 256) (.lit 0))

theorem rvv_shift_count_body_eval (cfg : Config) (s : State) (low : Nat) (bound : low < 256)
    (byte : s.locals "shift_byte" = some (.integer low)) :
    eval cfg s rvvShiftCountBody =
      some (.integer ((low : Int) - if 128 ≤ low then 256 else 0)) := by
  have cast := cast_i32_low low bound
  by_cases high : 128 ≤ low
  · simp [rvvShiftCountBody, eval, binary, truth, byte, cast, high, show (128 : Int) ≤ low by omega]
  · simp [rvvShiftCountBody, eval, binary, truth, byte, cast, high, show ¬ (128 : Int) ≤ low by omega]

theorem rvv_shift_count_eval_nat (cfg : Config) (s : State) (low : Nat) (bound : low < 256)
    (byte : s.locals "shift_byte" = some (.integer low)) :
    eval cfg s rvvShiftCountExpr =
      some (.integer ((low : Int) - if 128 ≤ low then 256 else 0)) := by
  have he := rvv_shift_count_body_eval cfg s low bound byte
  let count := (low : Int) - if 128 ≤ low then 256 else 0
  have valid : -2147483648 ≤ count ∧ count < 2147483648 := by
    dsimp [count]; split <;> constructor <;> omega
  change eval cfg s (.checkedSigned32 rvvShiftCountBody) = some (.integer count)
  rw [eval, he]
  change (if -2147483648 ≤ count ∧ count < 2147483648 then some (Value.integer count) else none) = _
  rw [if_pos valid]

theorem rvv_shift_count_eval (cfg : Config) (s : State) (raw : BitVec 32)
    (byte : s.locals "shift_byte" = some (.integer (((-raw).toNat % 256 : Nat) : Int))) :
    eval cfg s rvvShiftCountExpr = some (.integer (ShiftISA.rvvCount raw)) :=
  rvv_shift_count_eval_nat cfg s _ (Nat.mod_lt _ (by decide)) byte

end Salty.Kernels.QS8Add
