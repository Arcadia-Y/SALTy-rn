import Salty.Spec.QS8Add
import Salty.Proofs.QS8Add.Shift
import Salty.Proofs.Core.BinaryMemory

namespace Salty.Kernels.QS8Add
open CByte QuantizedAddISA
open SIMD.Arithmetic

def rvvProduct (p : Params) (a b : Byte) : BitVec 32 :=
  rvvMacc32 (multiply32 (extend16 (rvvSubWide a p.aZero)) p.aMultiplier)
    p.bMultiplier (extend16 (rvvSubWide b p.bZero))
def rvvFinish16 (p : Params) (x : BitVec 32) : BitVec 16 :=
  SIMD.Signed.addSat16 (rvvClip16RDN0 x) p.outputZero
def rvvFinish (p : Params) (x : BitVec 32) : Byte :=
  ByteISA.minSigned (ByteISA.maxSigned (SIMD.Signed.clipRDN0 (rvvFinish16 p x))
    p.outputMin) p.outputMax

theorem minSigned_eq (x y : Byte) : ByteISA.minSigned x y = min8 x y := by
  unfold ByteISA.minSigned min8
  split <;> split <;> try rfl
  · omega
  · apply BitVec.eq_of_toInt_eq; omega

theorem rvvFinish_product (p : Params) (a b : Byte) :
    rvvFinish p (ShiftISA.repairedShift (rvvProduct p a b) p.shift) = rvvLane p a b := by
  simp only [rvvFinish, minSigned_eq, rvvFinish16, rvvProduct, rvvLane,
    ByteISA.maxSigned, max8]

def loadAfter (s : State) (k : Nat) (as bs : List Byte) : State :=
  update (update (update s "vl" (.integer k)) "va" (.vector 1 as)) "vb" (.vector 1 bs)

def wideAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  let t := update s "vxa" (.halfwords (as.map (fun a => rvvSubWide a p.aZero)))
  let t := update t "vxb" (.halfwords (bs.map (fun b => rvvSubWide b p.bZero)))
  let t := update t "vxa32" (.words32 (as.map (fun a => extend16 (rvvSubWide a p.aZero))))
  update t "vxb32" (.words32 (bs.map (fun b => extend16 (rvvSubWide b p.bZero))))

def productAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  update s "vacc" (.words32 (List.zipWith (rvvProduct p) as bs))

def convertAfter (s : State) (p : Params) (xs : List (BitVec 32)) : State :=
  update (update s "vacc16" (.halfwords (xs.map (rvvFinish16 p))))
    "vout" (.vector 1 (xs.map (rvvFinish p)))

def storeAfter (s : State) (n k : Nat) (a b output : Address) (m : Memory) : State :=
  let t := { s with memory := m }
  let t := update t "input_a" (.pointer (a + BitVec.ofNat 64 k))
  let t := update t "input_b" (.pointer (b + BitVec.ofNat 64 k))
  let t := update t "output" (.pointer (output + BitVec.ofNat 64 k))
  update t "batch" (.integer (n - k : Nat))

set_option maxHeartbeats 1000000 in
theorem rvv_load_exec (cfg : Config) (s : State) (n : Nat) (a b : Address)
    (as bs : List Byte)
    (batch : s.locals "batch" = some (.integer n))
    (pa : s.locals "input_a" = some (.pointer a))
    (pb : s.locals "input_b" = some (.pointer b))
    (la : loadBytes s.memory a (cfg.choose n) = some as)
    (lb : loadBytes s.memory b (cfg.choose n) = some bs) :
    Exec cfg (takeStatements 3 rvvBody) s (loadAfter s (cfg.choose n) as bs) := by
  have cap : cfg.choose n ≤ cfg.capacity := Nat.le_trans (cfg.bounded n) (Nat.min_le_right ..)
  apply run_sound (fuel := 8)
  simp [takeStatements, rvvBody, rvvLoop, loopBody, firstStatement, dropStatements,
    Generated.QS8Add.rvv, run, eval, intrinsic, update, batch, pa, pb, la, lb, cap, loadAfter]

set_option maxHeartbeats 1000000 in
theorem rvv_wide_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte) (k : Nat)
    (vl : s.locals "vl" = some (.integer k))
    (va : s.locals "va" = some (.vector 1 as)) (vb : s.locals "vb" = some (.vector 1 bs))
    (za : s.locals "a_zero_point" = some (.integer p.aZero.toInt))
    (zb : s.locals "b_zero_point" = some (.integer p.bZero.toInt))
    (ha : as.length = k) (hb : bs.length = k) :
    Exec cfg (takeStatements 4 (dropStatements 3 rvvBody)) s (wideAfter s p as bs) := by
  have ta : as.take k = as := by simp [← ha]
  have tb : bs.take k = bs := by simp [← hb]
  apply run_sound (fuel := 8)
  simp [takeStatements, rvvBody, rvvLoop, loopBody, firstStatement, dropStatements,
    Generated.QS8Add.rvv, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic,
    integerArithmeticIntrinsic, update, vl, va, vb, za, zb, ha, hb, ta, tb, ← List.map_take,
    wideAfter, List.map_map, Function.comp_def]

set_option maxHeartbeats 1000000 in
theorem rvv_product_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte) (k : Nat)
    (vl : s.locals "vl" = some (.integer k))
    (va : s.locals "vxa32" = some (.words32 (as.map (fun a => extend16 (rvvSubWide a p.aZero)))))
    (vb : s.locals "vxb32" = some (.words32 (bs.map (fun b => extend16 (rvvSubWide b p.bZero)))))
    (ma : s.locals "a_multiplier" = some (.integer p.aMultiplier.toInt))
    (mb : s.locals "b_multiplier" = some (.integer p.bMultiplier.toInt))
    (ha : as.length = k) (hb : bs.length = k) :
    Exec cfg (takeStatements 2 (dropStatements 7 rvvBody)) s (productAfter s p as bs) := by
  have ta : as.take k = as := by simp [← ha]
  have tb : bs.take k = bs := by simp [← hb]
  apply run_sound (fuel := 8)
  simp +contextual [takeStatements, rvvBody, rvvLoop, loopBody, firstStatement, dropStatements,
    Generated.QS8Add.rvv, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic,
    integerArithmeticIntrinsic, update, vl, va, vb, ma, mb, ha, hb, ta, tb, ← List.map_take,
    productAfter, rvvProduct, List.map_map, Function.comp_def, List.zipWith_map] <;> rfl

set_option maxHeartbeats 1000000 in
theorem rvv_convert_exec (cfg : Config) (s : State) (p : Params) (xs : List (BitVec 32)) (k : Nat)
    (vl : s.locals "vl" = some (.integer k))
    (acc : s.locals "vacc" = some (.words32 xs))
    (zero : s.locals "output_zero_point" = some (.integer p.outputZero.toInt))
    (lo : s.locals "output_min" = some (.integer p.outputMin.toInt))
    (hi : s.locals "output_max" = some (.integer p.outputMax.toInt))
    (len : xs.length = k) :
    Exec cfg (takeStatements 5 (dropStatements 10 rvvBody)) s (convertAfter s p xs) := by
  have tx : xs.take k = xs := by simp [← len]
  have c0 : convert .u64 0 = 0 := rfl
  have r2 : convert .u32 2 = 2 := rfl
  apply run_sound (fuel := 9)
  simp +contextual [takeStatements, rvvBody, rvvLoop, loopBody, firstStatement, dropStatements,
    Generated.QS8Add.rvv, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic,
    integerArithmeticIntrinsic, scalarLanes, update, vl, acc, zero, lo, hi, len, tx, c0, r2,
    ← List.map_take, convertAfter, rvvFinish, rvvFinish16, List.map_map, Function.comp_def] <;> rfl

theorem rvv_store_exec (cfg : Config) (s : State) (n k : Nat) (a b output : Address)
    (xs : List Byte) (m : Memory) (bound : n < 2^64) (le : k ≤ n)
    (batch : s.locals "batch" = some (.integer n)) (vl : s.locals "vl" = some (.integer k))
    (pa : s.locals "input_a" = some (.pointer a)) (pb : s.locals "input_b" = some (.pointer b))
    (po : s.locals "output" = some (.pointer output))
    (vec : s.locals "vout" = some (.vector 1 xs)) (len : xs.length = k)
    (store : storeBytes s.memory output xs = some m) :
    Exec cfg (dropStatements 15 rvvBody) s (storeAfter s n k a b output m) := by
  have tx : xs.take k = xs := by simp [← len]
  apply run_sound (fuel := 9)
  simp [rvvBody, rvvLoop, loopBody, firstStatement, dropStatements, Generated.QS8Add.rvv,
    run, eval, effect, update, binary, batch, vl, pa, pb, po, vec, len, store, tx,
    storeAfter, cast_sub n k le bound]

end Salty.Kernels.QS8Add
