import Salty.Proofs.Rdsum.RvvStore

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

theorem readWords32_columns (m : Memory) (a : Address) (n : Nat) :
    readWords32 m a n = (List.range n).map (fun i => readWord32 m (a+BitVec.ofNat 64 (4*i))) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [readWords32, List.range_succ_eq_map, List.map_cons, List.map_map, ih]
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.cons.injEq, true_and]
    apply List.map_congr_left
    intro i hi
    congr 1
    simp only [Function.comp_def, Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
    change a+4+BitVec.ofNat 64 (4*i) = a+(BitVec.ofNat 64 (4*i)+4)
    ac_rfl

theorem intervalSum_zero (kind : Interpretation) (m : Memory) (input : Address)
    (stride rows column : Nat) :
    intervalSum kind m input stride 0 rows column = columnSum kind m input stride rows column := by
  simp [intervalSum, columnSum, columnBytes, BitVec.ofNat_add, BitVec.add_assoc]

theorem storedWords_columns (m : Memory) (output : Address) (width : Nat) (acc : Nat → BitVec 32) :
    storedWords m output width ((List.range width).map acc) =
      (List.range width).map (fun i => readWord32 m (output+BitVec.ofNat 64 (4*i))+acc i) := by
  rw [storedWords, readWords32_columns]
  exact WideningISA.zipWith_map_same _ _ _ _

end Salty.Kernels.Rdsum
