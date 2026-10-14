import Salty.Proofs.QS8Add.RvvBlocks
import Salty.Generated.QS8AddNeon

namespace Salty.Kernels.QS8Add
open CByte QuantizedAddISA
open SIMD.Arithmetic

structure NeonParams (s : State) (p : Params) : Prop where
  zeroA : s.locals "va_zero_point" = some (.vector 1 (List.replicate 8 p.aZero))
  zeroB : s.locals "vb_zero_point" = some (.vector 1 (List.replicate 8 p.bZero))
  multA : s.locals "va_multiplier" = some (.words32 (List.replicate 4 p.aMultiplier))
  multB : s.locals "vb_multiplier" = some (.words32 (List.replicate 4 p.bMultiplier))
  shift : s.locals "vright_shift" = some (.words32 (List.replicate 4 (-p.shift)))
  outputZero : s.locals "voutput_zero_point" = some (.halfwords (List.replicate 8 p.outputZero))
  outputMin : s.locals "voutput_min" = some (.vector 1 (List.replicate 16 p.outputMin))
  outputMax : s.locals "voutput_max" = some (.vector 1 (List.replicate 16 p.outputMax))

def neonWide (zero : Byte) (a : Byte) : BitVec 16 := neonSubWide a zero

def neonMultiply (p : Params) (a : Byte) : BitVec 32 :=
  multiply32 (extend16 (neonWide p.aZero a)) p.aMultiplier

def neonProduct (p : Params) (a b : Byte) : BitVec 32 :=
  neonMla32 (neonMultiply p a) (extend16 (neonWide p.bZero b)) p.bMultiplier

def neonFinish16 (p : Params) (x : BitVec 32) : BitVec 16 :=
  SIMD.Signed.addSat16 (neonNarrow16 x) p.outputZero

def neonFinish (p : Params) (x : BitVec 32) : Byte :=
  ByteISA.minSigned (ByteISA.maxSigned (SIMD.Signed.narrowSat8 (neonFinish16 p x))
    p.outputMin) p.outputMax

theorem neonFinish_product (p : Params) (a b : Byte) :
    neonFinish p (ShiftISA.neonShift (neonProduct p a b) p.shift) = neonLane p a b := by
  simp only [neonFinish, minSigned_eq, neonFinish16, neonProduct, neonMultiply,
    neonWide, neonLane, ByteISA.maxSigned, max8]

theorem zip_replicate_right {α β γ : Type} (f : α → β → γ) (xs : List α) (y : β) (n : Nat) :
    List.zipWith f xs (List.replicate n y) = (xs.take n).map (fun x => f x y) := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => cases n <;> simp [List.replicate_succ, ih]

theorem zip_four {α β γ : Type} (f : α → β → γ) (xs : List α) (y : β) :
    List.zipWith f xs [y,y,y,y] = (xs.take 4).map (fun x => f x y) :=
  zip_replicate_right f xs y 4

theorem zip_eight {α β γ : Type} (f : α → β → γ) (xs : List α) (y : β) :
    List.zipWith f xs [y,y,y,y,y,y,y,y] = (xs.take 8).map (fun x => f x y) :=
  zip_replicate_right f xs y 8

theorem mapped_split (f : α → β) (xs : List α) (n : Nat) :
    (xs.take n).map f ++ (xs.drop n).map f = xs.map f := by
  rw [← List.map_append, List.take_append_drop]

def neonTail : Stmt := firstStatement (dropStatements 14 Generated.QS8Add.neon)
def branchYes : Stmt → Stmt
  | .branch _ yes _ => yes
  | _ => .skip

def neonTailBody : Stmt := firstStatement (firstStatement (branchYes neonTail))

-- The tail's first sixteen statements calculate eight lanes, including padding.
def tailLoadAfter (s : State) (a b : Address) (as bs : List Byte) : State :=
  let t := update s "va01234567_2" (.vector 1 as)
  let t := update t "input_a" (.pointer (a + 8))
  let t := update t "vb01234567_2" (.vector 1 bs)
  update t "input_b" (.pointer (b + 8))

def tailSubAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  update (update s "vxa01234567_2" (.halfwords (as.map (neonWide p.aZero))))
    "vxb01234567_2" (.halfwords (bs.map (neonWide p.bZero)))

def tailMulAfter (s : State) (p : Params) (as : List Byte) : State :=
  update (update s "vacc0123_2" (.words32 ((as.take 4).map (neonMultiply p))))
    "vacc4567_2" (.words32 ((as.drop 4).map (neonMultiply p)))

def tailMlaAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  let xs := List.zipWith (neonProduct p) as bs
  update (update s "vacc0123_2" (.words32 (xs.take 4))) "vacc4567_2" (.words32 (xs.drop 4))

def tailShiftAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  let xs := (List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)
  update (update s "vacc0123_2" (.words32 (xs.take 4))) "vacc4567_2" (.words32 (xs.drop 4))

def tailNarrowAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  let xs := (List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)
  update s "vacc01234567_2" (.halfwords (xs.map (neonFinish16 p)))

def tailClampAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  update s "vout01234567" (.vector 1 (List.zipWith (neonLane p) as bs))

set_option maxHeartbeats 1000000 in
theorem tail_load_exec (cfg : Config) (s : State) (a b : Address) (as bs : List Byte)
    (pa : s.locals "input_a" = some (.pointer a)) (pb : s.locals "input_b" = some (.pointer b))
    (la : loadBytes s.memory a 8 = some as) (lb : loadBytes s.memory b 8 = some bs) :
    Exec cfg (takeStatements 4 neonTailBody) s (tailLoadAfter s a b as bs) := by
  apply run_sound (fuel := 8)
  simp +contextual [neonTailBody, neonTail, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, update, pa, pb, la, lb, tailLoadAfter]

set_option maxHeartbeats 1000000 in
theorem tail_sub_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (va : s.locals "va01234567_2" = some (.vector 1 as))
    (vb : s.locals "vb01234567_2" = some (.vector 1 bs))
    (za : s.locals "va_zero_point" = some (.vector 1 (List.replicate 8 p.aZero)))
    (zb : s.locals "vb_zero_point" = some (.vector 1 (List.replicate 8 p.bZero)))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 4 neonTailBody)) s (tailSubAfter s p as bs) := by
  have ta : as.take 8 = as := by simp [← ha]
  have tb : bs.take 8 = bs := by simp [← hb]
  apply run_sound (fuel := 6)
  simp [neonTailBody, neonTail, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, va, vb, za, zb, ha, hb, ta, tb, tailSubAfter, zip_replicate_right, zip_eight, neonWide] <;> rfl

set_option maxHeartbeats 1000000 in
theorem tail_mul_exec (cfg : Config) (s : State) (p : Params) (as : List Byte)
    (va : s.locals "vxa01234567_2" = some (.halfwords (as.map (neonWide p.aZero))))
    (ma : s.locals "va_multiplier" = some (.words32 (List.replicate 4 p.aMultiplier)))
    (ha : as.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 6 neonTailBody)) s (tailMulAfter s p as) := by
  have high : (as.drop 4).length = 4 := by simp [ha]
  have ht : (as.drop 4).take 4 = as.drop 4 := by apply List.take_of_length_le; omega
  apply run_sound (fuel := 6)
  simp [neonTailBody, neonTail, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, va, ma, ha, high, ht, tailMulAfter, zip_replicate_right, zip_four, ← List.map_take,
    ← List.map_drop, List.map_map, Function.comp_def, neonMultiply, List.take_take] <;> rfl

set_option maxHeartbeats 1000000 in
theorem tail_mla_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (accLo : s.locals "vacc0123_2" = some (.words32 ((as.take 4).map (neonMultiply p))))
    (accHi : s.locals "vacc4567_2" = some (.words32 ((as.drop 4).map (neonMultiply p))))
    (vb : s.locals "vxb01234567_2" = some (.halfwords (bs.map (neonWide p.bZero))))
    (mb : s.locals "vb_multiplier" = some (.words32 (List.replicate 4 p.bMultiplier)))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 8 neonTailBody)) s (tailMlaAfter s p as bs) := by
  have ta : (as.drop 4).take 4 = as.drop 4 := by apply List.take_of_length_le; simp [ha]
  have tb : (bs.drop 4).take 4 = bs.drop 4 := by apply List.take_of_length_le; simp [hb]
  apply run_sound (fuel := 6)
  simp [neonTailBody, neonTail, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, accLo, accHi, vb, mb, ha, hb, tailMlaAfter, zip_replicate_right, zip_four, List.zip_eq_zipWith, List.map_zipWith,
    ← List.map_take, ← List.map_drop, List.map_map, Function.comp_def,
    List.zipWith_map, List.take_zipWith, List.drop_zipWith, neonProduct, List.take_take, ta, tb] <;> rfl

set_option maxHeartbeats 1000000 in
theorem tail_shift_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (accLo : s.locals "vacc0123_2" = some (.words32 ((List.zipWith (neonProduct p) as bs).take 4)))
    (accHi : s.locals "vacc4567_2" = some (.words32 ((List.zipWith (neonProduct p) as bs).drop 4)))
    (shift : s.locals "vright_shift" = some (.words32 (List.replicate 4 (-p.shift))))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 10 neonTailBody)) s (tailShiftAfter s p as bs) := by
  have len : (List.zipWith (neonProduct p) as bs).length = 8 := by simp [ha, hb]
  have th : ((List.zipWith (neonProduct p) as bs).drop 4).take 4 =
      (List.zipWith (neonProduct p) as bs).drop 4 := by apply List.take_of_length_le; simp [len]
  apply run_sound (fuel := 6)
  simp [neonTailBody, neonTail, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, accLo, accHi, shift, ha, hb, len, th, tailShiftAfter, zip_replicate_right, zip_four,
    ← List.map_take, ← List.map_drop, List.take_take, ShiftISA.neonShift] <;> rfl

set_option maxHeartbeats 1000000 in
theorem tail_narrow_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (accLo : s.locals "vacc0123_2" = some (.words32 (((List.zipWith (neonProduct p) as bs).map
      (fun x => ShiftISA.neonShift x p.shift)).take 4)))
    (accHi : s.locals "vacc4567_2" = some (.words32 (((List.zipWith (neonProduct p) as bs).map
      (fun x => ShiftISA.neonShift x p.shift)).drop 4)))
    (zero : s.locals "voutput_zero_point" = some (.halfwords (List.replicate 8 p.outputZero)))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 1 (dropStatements 12 neonTailBody)) s (tailNarrowAfter s p as bs) := by
  let xs := (List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)
  have len : xs.length = 8 := by simp [xs, ha, hb]
  change s.locals "vacc0123_2" = some (.words32 (xs.take 4)) at accLo
  change s.locals "vacc4567_2" = some (.words32 (xs.drop 4)) at accHi
  have full : xs.take 8 = xs := by apply List.take_of_length_le; omega
  change Exec cfg _ s (update s "vacc01234567_2" (.halfwords (xs.map (neonFinish16 p))))
  apply run_sound (fuel := 5)
  simp [neonTailBody, neonTail, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, accLo, accHi, zero, len, full, zip_replicate_right, zip_eight,
    mapped_split, ← List.map_take, ← List.map_drop, List.map_map, Function.comp_def, neonFinish16] <;> rfl

def clampHalf (p : Params) (x : BitVec 16) : Byte :=
  ByteISA.minSigned (ByteISA.maxSigned (SIMD.Signed.narrowSat8 x) p.outputMin) p.outputMax

set_option maxHeartbeats 1000000 in
theorem tail_clamp_raw_exec (cfg : Config) (s : State) (p : Params) (xs : List (BitVec 16))
    (acc : s.locals "vacc01234567_2" = some (.halfwords xs))
    (lo : s.locals "voutput_min" = some (.vector 1 (List.replicate 16 p.outputMin)))
    (hi : s.locals "voutput_max" = some (.vector 1 (List.replicate 16 p.outputMax)))
    (len : xs.length = 8) :
    Exec cfg (takeStatements 3 (dropStatements 13 neonTailBody)) s
      (update s "vout01234567" (.vector 1 (xs.map (clampHalf p)))) := by
  have full : xs.take 8 = xs := List.take_of_length_le (by omega)
  apply run_sound (fuel := 7)
  simp +contextual [neonTailBody, neonTail, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, zipLanes,
    update, acc, lo, hi, len, full, zip_replicate_right, zip_eight,
    ← List.map_take, List.take_take, List.map_map, Function.comp_def, clampHalf] <;> rfl

theorem tail_clamp_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (acc : s.locals "vacc01234567_2" = some (.halfwords
      (((List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)).map (neonFinish16 p))))
    (lo : s.locals "voutput_min" = some (.vector 1 (List.replicate 16 p.outputMin)))
    (hi : s.locals "voutput_max" = some (.vector 1 (List.replicate 16 p.outputMax)))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 3 (dropStatements 13 neonTailBody)) s (tailClampAfter s p as bs) := by
  have eq : (((List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)).map
      (neonFinish16 p)).map (clampHalf p) = List.zipWith (neonLane p) as bs := by
    simp only [List.map_map, List.map_zipWith, Function.comp_def]
    change List.zipWith (fun a b => neonFinish p (ShiftISA.neonShift (neonProduct p a b) p.shift)) as bs = _
    simp only [neonFinish_product]
  have h := tail_clamp_raw_exec cfg s p _ acc lo hi (by simp [ha, hb])
  simpa only [eq] using h

end Salty.Kernels.QS8Add
