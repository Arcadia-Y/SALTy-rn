import Salty.Proofs.Core.CRowSum
import Salty.Proofs.Rdsum.Zero

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

/-- Actual active-prefix load; permissions are checked for every input byte. -/
theorem rvv_load_exec (cfg : Config) (s : State) (destination source : String)
    (address : Address) (n : Nat) (cap : n ≤ cfg.capacity)
    (ptr : s.locals source = some (.pointer address))
    (vl : s.locals "vl" = some (.integer n))
    (readable : ∀ a, Footprint address n a → s.memory.readable a = true) :
    Exec cfg (.assign destination (.call .loadRVV [.var source, .var "vl"])) s
      (update s destination (.vector 1 (readBytes s.memory address n))) := by
  apply Exec.assign
  simp [eval, ptr, vl, intrinsic, cap, loadBytes_success _ _ _ readable]

theorem rvv_add_byte_exec (kind : Interpretation) (cfg : Config) (s : State) (source : String)
    (n : Nat) (acc : List (BitVec 16)) (xs : List Byte)
    (ha : acc.length = n) (hx : xs.length = n) (cap : n ≤ cfg.capacity)
    (vacc : s.locals "vacc16" = some (.halfwords acc))
    (vin : s.locals source = some (.vector 1 xs))
    (vl : s.locals "vl" = some (.integer n)) :
    Exec cfg (.assign "vacc16" (.call (rowByteRVVPrim kind) [.var "vacc16", .var source, .var "vl"])) s
      (update s "vacc16" (.halfwords (WideningISA.widenAdd16 kind acc xs))) := by
  apply Exec.assign
  simp only [eval, vacc, vin, vl, List.mapM_cons, List.mapM_nil, Option.bind_some, pure, bind]
  exact row_byte_rvv_intrinsic kind cfg s.memory n acc xs ha hx cap

/-- Explicit word-to-byte-pointer cast sequence used by every row increment. -/
theorem row_pointer_exec (cfg : Config) (s : State) (name : String) (a : Address) (increment : Nat)
    (ptr : s.locals name = some (.pointer a))
    (step : s.locals "input_increment" = some (.integer increment)) :
    Exec cfg (.assign name (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var name))
      (.var "input_increment"))))) s (update s name (.pointer (a+BitVec.ofNat 64 increment))) := by
  have cast : BitVec.ofInt 64 (convert .u64 ((a.toNat : Int)+increment)) = a+BitVec.ofNat 64 increment := by
    simp only [convert, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_natCast]
    simp
  apply Exec.assign
  simp only [eval, ptr, step, pure, bind, Option.bind_some, binary]
  rw [cast]

/-- Signed source-level loop arithmetic is checked even when the new value is
negative: the last seven-row step may leave current_batch in [-6,0]. -/
theorem group_decrement_exec (cfg : Config) (s : State) (r : Int)
    (hr : s.locals "current_batch" = some (.integer r)) (lo : 0 < r) (hi : r ≤ 252) :
    Exec cfg (.assign "current_batch" (.checkedSigned32 (.bin .sub (.var "current_batch") (.lit 7)))) s
      (update s "current_batch" (.integer (r-7))) := by
  have bounds : -(2^31) ≤ r-7 ∧ r-7 < 2^31 := by omega
  apply Exec.assign
  simp [eval, hr, binary, bounds]
  omega

end Salty.Kernels.Rdsum
