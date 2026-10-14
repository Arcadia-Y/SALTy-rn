import Salty.Generated.QS8AddRvv
import Salty.Proofs.Core.CByteSyntax

set_option maxHeartbeats 1000000
namespace Salty.Kernels.QS8Add
open CByte

def rvvLoop : Stmt := firstStatement (dropStatements 14 Generated.QS8Add.rvv)
def rvvBody : Stmt := loopBody rvvLoop
def rvvShiftBlock : Stmt := firstStatement (dropStatements 9 rvvBody)

theorem rvvShiftBlock_shape : rvvShiftBlock =
  .branch (.or (.bin .le (.var "shift") (.negSigned32 (.lit 32)))
    (.bin .ge (.var "shift") (.lit 32)))
    (.seq (.assign "vacc" (.call .dupI32RVV [.lit 0, .var "vl"])) .skip)
    (.branch (.bin .lt (.var "shift") (.lit 0))
      (.seq (.assign "vacc" (.call .rightRNU32RVV [.var "vacc",
        .cast .u64 (.negSigned32 (.var "shift")), .cast .u32 (.lit 0), .var "vl"])) .skip)
      (.seq (.assign "vacc" (.call .leftI32RVV [.var "vacc",
        .cast .u64 (.var "shift"), .var "vl"])) .skip)) := by rfl

theorem count_bounds (raw : BitVec 32) :
    -128 ≤ ShiftISA.rvvCount raw ∧ ShiftISA.rvvCount raw < 128 := by
  rw [← ShiftISA.count_eq]
  unfold ShiftISA.neonCount
  have lo := BitVec.le_toInt ((-raw).setWidth 8)
  have hi := BitVec.toInt_lt (x := (-raw).setWidth 8)
  constructor <;> omega

set_option maxHeartbeats 2000000 in
/-- Exact extracted target shift block, including its zero/right/left control
flow and checked scalar negation. This does not assume the arithmetic equality
with NEON; it establishes execution before the lane theorem is applied. -/
theorem rvv_shift_count_exec (cfg : Config) (s : State) (count : Int)
    (xs : List (BitVec 32)) (vl : Nat)
    (hshift : s.locals "shift" = some (.integer (count)))
    (hacc : s.locals "vacc" = some (.words32 xs))
    (hvl : s.locals "vl" = some (.integer vl))
    (hlen : xs.length = vl) (hcap : vl ≤ cfg.capacity)
    (bounds : -128 ≤ count ∧ count < 128) :
    Exec cfg rvvShiftBlock s (update s "vacc" (.words32 (xs.map (fun x => if count ≤ -32 ∨ 32 ≤ count then 0 else if count < 0 then ShiftISA.rvvRight x (-count).toNat else ShiftISA.rvvLeft x count.toNat)))) := by
  rw [rvvShiftBlock_shape]
  have c0 : convert .u32 0 = 0 := rfl
  have neg32 : -(2^31 : Int) < 32 ∧ (32 : Int) < 2^31 := by decide
  have cast_count (x : Int) (hx : 0 ≤ x) (hb : x < 128) : convert .u64 x = x := by
    have eq : (x.toNat : Int) = x := Int.toNat_of_nonneg hx
    rw [← eq]
    exact cast_nat _ (by omega)
  by_cases lo : count ≤ -32
  · simp only [lo, true_or, ↓reduceIte]
    apply Exec.yes (v := .integer 1)
    · simp [eval, binary, truth, hshift, neg32, lo]
    · rfl
    · apply Exec.seq (b := .skip) ?_ Exec.skip
      apply Exec.assign
      simp [eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
        hvl, hcap, hlen, List.map_const']
  · by_cases hi : 32 ≤ count
    · simp only [hi, or_true, ↓reduceIte]
      apply Exec.yes (v := .integer 1)
      · simp [eval, binary, truth, hshift, neg32, lo, hi]
      · rfl
      · apply Exec.seq (b := .skip) ?_ Exec.skip
        apply Exec.assign
        simp [eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
          hvl, hcap, hlen, List.map_const']
    · simp only [lo, hi, or_self, ↓reduceIte]
      apply Exec.no (v := .integer 0)
      · simp [eval, binary, truth, hshift, neg32, lo, hi]
      · rfl
      · by_cases neg : count < 0
        · simp only [neg, ↓reduceIte]
          apply Exec.yes (v := .integer 1)
          · simp [eval, binary, hshift, neg]
          · rfl
          · have valid : -(2^31 : Int) < count ∧ count < 2^31 := by omega
            change -2147483648 < count ∧ count < 2147483648 at valid
            have nn : 0 ≤ -count := by omega
            have cc := cast_count (-count) nn (by omega)
            apply Exec.seq (b := .skip) ?_ Exec.skip
            apply Exec.assign
            simp [eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
              hacc, hvl, hshift, valid, cc, c0, nn, show count ≤ 0 by omega, ← hlen, ← List.map_take]
        · simp only [neg, ↓reduceIte]
          apply Exec.no (v := .integer 0)
          · simp [eval, binary, hshift, neg]
          · rfl
          · have nn : 0 ≤ count := by omega
            have cc := cast_count count nn (by omega)
            apply Exec.seq (b := .skip) ?_ Exec.skip
            apply Exec.assign
            simp [eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
              hacc, hvl, hshift, cc, nn, ← hlen, ← List.map_take]

/-- The extracted branch computes exactly the repaired instruction-level map
for every active lane and every raw parameter bit pattern. -/
theorem rvv_shift_exec (cfg : Config) (s : State) (raw : BitVec 32)
    (xs : List (BitVec 32)) (vl : Nat)
    (hshift : s.locals "shift" = some (.integer (ShiftISA.rvvCount raw)))
    (hacc : s.locals "vacc" = some (.words32 xs))
    (hvl : s.locals "vl" = some (.integer vl))
    (hlen : xs.length = vl) (hcap : vl ≤ cfg.capacity) :
    Exec cfg rvvShiftBlock s
      (update s "vacc" (.words32 (xs.map (fun x => ShiftISA.repairedShift x raw)))) :=
  rvv_shift_count_exec cfg s _ xs vl hshift hacc hvl hlen hcap (count_bounds raw)

end Salty.Kernels.QS8Add
