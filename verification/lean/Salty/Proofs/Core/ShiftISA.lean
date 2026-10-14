import Salty.Spec.QuantizedShift
import Std

/-! Signed variable shift lanes for quantized addition. These supporting
instruction lemmas do not establish execution of either complete C kernel. -/
namespace Salty.ShiftISA

theorem count_eq (raw : BitVec 32) : neonCount raw = rvvCount raw := by
  unfold neonCount rvvCount
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_setWidth]
  split <;> split <;> omega

theorem rounded_width_zero (x : BitVec 32) :
    x.sshiftRight 32 + roundBit x 32 = 0 := by
  unfold roundBit
  rw [← BitVec.msb_eq_getLsbD_last]
  cases h : x.msb
  · simp [BitVec.sshiftRight_eq_of_msb_false h, BitVec.ushiftRight_eq_zero (Nat.le_refl 32)]
  · simp [BitVec.sshiftRight_eq_of_msb_true h, BitVec.ushiftRight_eq_zero (Nat.le_refl 32)]

theorem shift_eq (x raw : BitVec 32) : neonShift x raw = repairedShift x raw := by
  change (if 0 ≤ neonCount raw then x <<< (neonCount raw).toNat
    else neonRight x (-(neonCount raw)).toNat) = repairedShift x raw
  unfold repairedShift
  rw [count_eq]
  generalize rvvCount raw = c
  by_cases lo : c ≤ -32
  · have hn : 32 ≤ (-c).toNat := by omega
    simp [lo, show ¬0 ≤ c by omega, neonRight, Nat.min_eq_right hn, rounded_width_zero]
  · by_cases hi : 32 ≤ c
    · have hn : 32 ≤ c.toNat := by omega
      simp [hi, show 0 ≤ c by omega, BitVec.shiftLeft_eq_zero hn]
    · by_cases neg : c < 0
      · have hn : (-c).toNat < 32 := by omega
        have hz : (-c).toNat ≠ 0 := by omega
        simp [lo, hi, neg, show ¬0 ≤ c by omega, neonRight, rvvRight,
          Nat.min_eq_left (Nat.le_of_lt hn), Nat.mod_eq_of_lt hn, hz]
      · have hn : c.toNat < 32 := by omega
        simp [lo, hi, neg, show 0 ≤ c by omega, rvvLeft, Nat.mod_eq_of_lt hn]

theorem old_shift_counterexample :
    neonShift 1 32 = 0 ∧ rvvRight 1 32 = 1 := by decide

end Salty.ShiftISA
