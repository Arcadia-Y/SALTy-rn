import Salty.Proofs.QS8Add.NeonLanes

namespace Salty.Kernels.QS8Add
open CByte QuantizedAddISA
open SIMD.Arithmetic

def neonMainLoop : Stmt := firstStatement (dropStatements 13 Generated.QS8Add.neon)
def neonMainBody : Stmt := loopBody neonMainLoop
def neonMainCode : Stmt := firstStatement neonMainBody

def mainFirstLoadAfter (s : State) (a b : Address) (as bs : List Byte) : State :=
  let t := update s "va01234567" (.vector 1 as)
  let t := update t "input_a" (.pointer (a + 8))
  let t := update t "vb01234567" (.vector 1 bs)
  update t "input_b" (.pointer (b + 8))

def mainFirstSubAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  update (update s "vxa01234567" (.halfwords (as.map (neonWide p.aZero))))
    "vxb01234567" (.halfwords (bs.map (neonWide p.bZero)))

def mainFirstMulAfter (s : State) (p : Params) (as : List Byte) : State :=
  update (update s "vacc0123" (.words32 ((as.take 4).map (neonMultiply p))))
    "vacc4567" (.words32 ((as.drop 4).map (neonMultiply p)))

def mainFirstMlaAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  let xs := List.zipWith (neonProduct p) as bs
  update (update s "vacc0123" (.words32 (xs.take 4))) "vacc4567" (.words32 (xs.drop 4))

def mainFirstShiftAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  let xs := (List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)
  update (update s "vacc0123" (.words32 (xs.take 4))) "vacc4567" (.words32 (xs.drop 4))

def mainFirstNarrowAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  let xs := (List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)
  update s "vacc01234567" (.halfwords (xs.map (neonFinish16 p)))

set_option maxHeartbeats 1000000 in
theorem main_first_load_exec (cfg : Config) (s : State) (a b : Address) (as bs : List Byte)
    (pa : s.locals "input_a" = some (.pointer a)) (pb : s.locals "input_b" = some (.pointer b))
    (la : loadBytes s.memory a 8 = some as) (lb : loadBytes s.memory b 8 = some bs) :
    Exec cfg (takeStatements 4 (dropStatements 0 neonMainCode)) s (mainFirstLoadAfter s a b as bs) := by
  apply run_sound (fuel := 8)
  simp +contextual [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, update, pa, pb, la, lb, mainFirstLoadAfter]

set_option maxHeartbeats 1000000 in
theorem main_first_sub_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (va : s.locals "va01234567" = some (.vector 1 as))
    (vb : s.locals "vb01234567" = some (.vector 1 bs))
    (za : s.locals "va_zero_point" = some (.vector 1 (List.replicate 8 p.aZero)))
    (zb : s.locals "vb_zero_point" = some (.vector 1 (List.replicate 8 p.bZero)))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 8 neonMainCode)) s (mainFirstSubAfter s p as bs) := by
  have ta : as.take 8 = as := by simp [← ha]
  have tb : bs.take 8 = bs := by simp [← hb]
  apply run_sound (fuel := 6)
  simp [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, va, vb, za, zb, ha, hb, ta, tb, mainFirstSubAfter, zip_replicate_right, zip_eight, neonWide] <;> rfl

set_option maxHeartbeats 1000000 in
theorem main_first_mul_exec (cfg : Config) (s : State) (p : Params) (as : List Byte)
    (va : s.locals "vxa01234567" = some (.halfwords (as.map (neonWide p.aZero))))
    (ma : s.locals "va_multiplier" = some (.words32 (List.replicate 4 p.aMultiplier)))
    (ha : as.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 12 neonMainCode)) s (mainFirstMulAfter s p as) := by
  have high : (as.drop 4).length = 4 := by simp [ha]
  have ht : (as.drop 4).take 4 = as.drop 4 := by apply List.take_of_length_le; omega
  apply run_sound (fuel := 6)
  simp [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, va, ma, ha, high, ht, mainFirstMulAfter, zip_replicate_right, zip_four, ← List.map_take,
    ← List.map_drop, List.map_map, Function.comp_def, neonMultiply, List.take_take] <;> rfl

set_option maxHeartbeats 1000000 in
theorem main_first_mla_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (accLo : s.locals "vacc0123" = some (.words32 ((as.take 4).map (neonMultiply p))))
    (accHi : s.locals "vacc4567" = some (.words32 ((as.drop 4).map (neonMultiply p))))
    (vb : s.locals "vxb01234567" = some (.halfwords (bs.map (neonWide p.bZero))))
    (mb : s.locals "vb_multiplier" = some (.words32 (List.replicate 4 p.bMultiplier)))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 16 neonMainCode)) s (mainFirstMlaAfter s p as bs) := by
  have ta : (as.drop 4).take 4 = as.drop 4 := by apply List.take_of_length_le; simp [ha]
  have tb : (bs.drop 4).take 4 = bs.drop 4 := by apply List.take_of_length_le; simp [hb]
  apply run_sound (fuel := 6)
  simp [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, accLo, accHi, vb, mb, ha, hb, mainFirstMlaAfter, zip_replicate_right, zip_four, List.zip_eq_zipWith, List.map_zipWith,
    ← List.map_take, ← List.map_drop, List.map_map, Function.comp_def,
    List.zipWith_map, List.take_zipWith, List.drop_zipWith, neonProduct, List.take_take, ta, tb] <;> rfl

set_option maxHeartbeats 1000000 in
theorem main_first_shift_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (accLo : s.locals "vacc0123" = some (.words32 ((List.zipWith (neonProduct p) as bs).take 4)))
    (accHi : s.locals "vacc4567" = some (.words32 ((List.zipWith (neonProduct p) as bs).drop 4)))
    (shift : s.locals "vright_shift" = some (.words32 (List.replicate 4 (-p.shift))))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 20 neonMainCode)) s (mainFirstShiftAfter s p as bs) := by
  have len : (List.zipWith (neonProduct p) as bs).length = 8 := by simp [ha, hb]
  have th : ((List.zipWith (neonProduct p) as bs).drop 4).take 4 =
      (List.zipWith (neonProduct p) as bs).drop 4 := by apply List.take_of_length_le; simp [len]
  apply run_sound (fuel := 6)
  simp [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, accLo, accHi, shift, ha, hb, len, th, mainFirstShiftAfter, zip_replicate_right, zip_four,
    ← List.map_take, ← List.map_drop, List.take_take, ShiftISA.neonShift] <;> rfl

set_option maxHeartbeats 1000000 in
theorem main_first_narrow_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (accLo : s.locals "vacc0123" = some (.words32 (((List.zipWith (neonProduct p) as bs).map
      (fun x => ShiftISA.neonShift x p.shift)).take 4)))
    (accHi : s.locals "vacc4567" = some (.words32 (((List.zipWith (neonProduct p) as bs).map
      (fun x => ShiftISA.neonShift x p.shift)).drop 4)))
    (zero : s.locals "voutput_zero_point" = some (.halfwords (List.replicate 8 p.outputZero)))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 1 (dropStatements 24 neonMainCode)) s (mainFirstNarrowAfter s p as bs) := by
  let xs := (List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)
  have len : xs.length = 8 := by simp [xs, ha, hb]
  change s.locals "vacc0123" = some (.words32 (xs.take 4)) at accLo
  change s.locals "vacc4567" = some (.words32 (xs.drop 4)) at accHi
  have full : xs.take 8 = xs := by apply List.take_of_length_le; omega
  change Exec cfg _ s (update s "vacc01234567" (.halfwords (xs.map (neonFinish16 p))))
  apply run_sound (fuel := 5)
  simp [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, accLo, accHi, zero, len, full, zip_replicate_right, zip_eight,
    mapped_split, ← List.map_take, ← List.map_drop, List.map_map, Function.comp_def, neonFinish16] <;> rfl


def mainSecondLoadAfter (s : State) (a b : Address) (as bs : List Byte) : State :=
  let t := update s "va89ABCDEF" (.vector 1 as)
  let t := update t "input_a" (.pointer (a + 8))
  let t := update t "vb89ABCDEF" (.vector 1 bs)
  update t "input_b" (.pointer (b + 8))

def mainSecondSubAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  update (update s "vxa89ABCDEF" (.halfwords (as.map (neonWide p.aZero))))
    "vxb89ABCDEF" (.halfwords (bs.map (neonWide p.bZero)))

def mainSecondMulAfter (s : State) (p : Params) (as : List Byte) : State :=
  update (update s "vacc89AB" (.words32 ((as.take 4).map (neonMultiply p))))
    "vaccCDEF" (.words32 ((as.drop 4).map (neonMultiply p)))

def mainSecondMlaAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  let xs := List.zipWith (neonProduct p) as bs
  update (update s "vacc89AB" (.words32 (xs.take 4))) "vaccCDEF" (.words32 (xs.drop 4))

def mainSecondShiftAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  let xs := (List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)
  update (update s "vacc89AB" (.words32 (xs.take 4))) "vaccCDEF" (.words32 (xs.drop 4))

def mainSecondNarrowAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  let xs := (List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)
  update s "vacc89ABCDEF" (.halfwords (xs.map (neonFinish16 p)))

set_option maxHeartbeats 1000000 in
theorem main_second_load_exec (cfg : Config) (s : State) (a b : Address) (as bs : List Byte)
    (pa : s.locals "input_a" = some (.pointer a)) (pb : s.locals "input_b" = some (.pointer b))
    (la : loadBytes s.memory a 8 = some as) (lb : loadBytes s.memory b 8 = some bs) :
    Exec cfg (takeStatements 4 (dropStatements 4 neonMainCode)) s (mainSecondLoadAfter s a b as bs) := by
  apply run_sound (fuel := 8)
  simp +contextual [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, update, pa, pb, la, lb, mainSecondLoadAfter]

set_option maxHeartbeats 1000000 in
theorem main_second_sub_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (va : s.locals "va89ABCDEF" = some (.vector 1 as))
    (vb : s.locals "vb89ABCDEF" = some (.vector 1 bs))
    (za : s.locals "va_zero_point" = some (.vector 1 (List.replicate 8 p.aZero)))
    (zb : s.locals "vb_zero_point" = some (.vector 1 (List.replicate 8 p.bZero)))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 10 neonMainCode)) s (mainSecondSubAfter s p as bs) := by
  have ta : as.take 8 = as := by simp [← ha]
  have tb : bs.take 8 = bs := by simp [← hb]
  apply run_sound (fuel := 6)
  simp [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, va, vb, za, zb, ha, hb, ta, tb, mainSecondSubAfter, zip_replicate_right, zip_eight, neonWide] <;> rfl

set_option maxHeartbeats 1000000 in
theorem main_second_mul_exec (cfg : Config) (s : State) (p : Params) (as : List Byte)
    (va : s.locals "vxa89ABCDEF" = some (.halfwords (as.map (neonWide p.aZero))))
    (ma : s.locals "va_multiplier" = some (.words32 (List.replicate 4 p.aMultiplier)))
    (ha : as.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 14 neonMainCode)) s (mainSecondMulAfter s p as) := by
  have high : (as.drop 4).length = 4 := by simp [ha]
  have ht : (as.drop 4).take 4 = as.drop 4 := by apply List.take_of_length_le; omega
  apply run_sound (fuel := 6)
  simp [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, va, ma, ha, high, ht, mainSecondMulAfter, zip_replicate_right, zip_four, ← List.map_take,
    ← List.map_drop, List.map_map, Function.comp_def, neonMultiply, List.take_take] <;> rfl

set_option maxHeartbeats 1000000 in
theorem main_second_mla_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (accLo : s.locals "vacc89AB" = some (.words32 ((as.take 4).map (neonMultiply p))))
    (accHi : s.locals "vaccCDEF" = some (.words32 ((as.drop 4).map (neonMultiply p))))
    (vb : s.locals "vxb89ABCDEF" = some (.halfwords (bs.map (neonWide p.bZero))))
    (mb : s.locals "vb_multiplier" = some (.words32 (List.replicate 4 p.bMultiplier)))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 18 neonMainCode)) s (mainSecondMlaAfter s p as bs) := by
  have ta : (as.drop 4).take 4 = as.drop 4 := by apply List.take_of_length_le; simp [ha]
  have tb : (bs.drop 4).take 4 = bs.drop 4 := by apply List.take_of_length_le; simp [hb]
  apply run_sound (fuel := 6)
  simp [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, accLo, accHi, vb, mb, ha, hb, mainSecondMlaAfter, zip_replicate_right, zip_four, List.zip_eq_zipWith, List.map_zipWith,
    ← List.map_take, ← List.map_drop, List.map_map, Function.comp_def,
    List.zipWith_map, List.take_zipWith, List.drop_zipWith, neonProduct, List.take_take, ta, tb] <;> rfl

set_option maxHeartbeats 1000000 in
theorem main_second_shift_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (accLo : s.locals "vacc89AB" = some (.words32 ((List.zipWith (neonProduct p) as bs).take 4)))
    (accHi : s.locals "vaccCDEF" = some (.words32 ((List.zipWith (neonProduct p) as bs).drop 4)))
    (shift : s.locals "vright_shift" = some (.words32 (List.replicate 4 (-p.shift))))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 2 (dropStatements 22 neonMainCode)) s (mainSecondShiftAfter s p as bs) := by
  have len : (List.zipWith (neonProduct p) as bs).length = 8 := by simp [ha, hb]
  have th : ((List.zipWith (neonProduct p) as bs).drop 4).take 4 =
      (List.zipWith (neonProduct p) as bs).drop 4 := by apply List.take_of_length_le; simp [len]
  apply run_sound (fuel := 6)
  simp [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, accLo, accHi, shift, ha, hb, len, th, mainSecondShiftAfter, zip_replicate_right, zip_four,
    ← List.map_take, ← List.map_drop, List.take_take, ShiftISA.neonShift] <;> rfl

set_option maxHeartbeats 1000000 in
theorem main_second_narrow_exec (cfg : Config) (s : State) (p : Params) (as bs : List Byte)
    (accLo : s.locals "vacc89AB" = some (.words32 (((List.zipWith (neonProduct p) as bs).map
      (fun x => ShiftISA.neonShift x p.shift)).take 4)))
    (accHi : s.locals "vaccCDEF" = some (.words32 (((List.zipWith (neonProduct p) as bs).map
      (fun x => ShiftISA.neonShift x p.shift)).drop 4)))
    (zero : s.locals "voutput_zero_point" = some (.halfwords (List.replicate 8 p.outputZero)))
    (ha : as.length = 8) (hb : bs.length = 8) :
    Exec cfg (takeStatements 1 (dropStatements 25 neonMainCode)) s (mainSecondNarrowAfter s p as bs) := by
  let xs := (List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)
  have len : xs.length = 8 := by simp [xs, ha, hb]
  change s.locals "vacc89AB" = some (.words32 (xs.take 4)) at accLo
  change s.locals "vaccCDEF" = some (.words32 (xs.drop 4)) at accHi
  have full : xs.take 8 = xs := by apply List.take_of_length_le; omega
  change Exec cfg _ s (update s "vacc89ABCDEF" (.halfwords (xs.map (neonFinish16 p))))
  apply run_sound (fuel := 5)
  simp [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements, takeStatements, branchYes,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
    update, accLo, accHi, zero, len, full, zip_replicate_right, zip_eight,
    mapped_split, ← List.map_take, ← List.map_drop, List.map_map, Function.comp_def, neonFinish16] <;> rfl


theorem zip_sixteen {α β γ : Type} (f : α → β → γ) (xs : List α) (y : β) :
    List.zipWith f xs [y,y,y,y,y,y,y,y,y,y,y,y,y,y,y,y] =
      (xs.take 16).map (fun x => f x y) := zip_replicate_right f xs y 16

set_option maxHeartbeats 1000000 in
theorem main_clamp_raw_exec (cfg : Config) (s : State) (p : Params)
    (xs ys : List (BitVec 16))
    (accFirst : s.locals "vacc01234567" = some (.halfwords xs))
    (accSecond : s.locals "vacc89ABCDEF" = some (.halfwords ys))
    (lo : s.locals "voutput_min" = some (.vector 1 (List.replicate 16 p.outputMin)))
    (hi : s.locals "voutput_max" = some (.vector 1 (List.replicate 16 p.outputMax)))
    (hx : xs.length = 8) (hy : ys.length = 8) :
    Exec cfg (takeStatements 3 (dropStatements 26 neonMainCode)) s
      (update s "vout0123456789ABCDEF" (.vector 1 ((xs ++ ys).map (clampHalf p)))) := by
  have tx : xs.take 8 = xs := List.take_of_length_le (by omega)
  have ty : ys.take 8 = ys := List.take_of_length_le (by omega)
  have full : (xs ++ ys).take 16 = xs ++ ys := List.take_of_length_le (by simp [hx, hy])
  apply run_sound (fuel := 7)
  simp +contextual [neonMainCode, neonMainBody, neonMainLoop, loopBody,
    firstStatement, dropStatements, takeStatements,
    Generated.QS8Add.neon, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic,
    integerArithmeticIntrinsic, zipLanes, update, accFirst, accSecond, lo, hi, hx, hy, tx, ty,
    full, zip_replicate_right, zip_sixteen, ← List.map_append,
    ← List.map_take, List.take_take, List.map_map, Function.comp_def, clampHalf] <;> rfl

def mainClampAfter (s : State) (p : Params) (as bs cs ds : List Byte) : State :=
  update s "vout0123456789ABCDEF" (.vector 1
    (List.zipWith (neonLane p) as bs ++ List.zipWith (neonLane p) cs ds))

theorem main_clamp_exec (cfg : Config) (s : State) (p : Params) (as bs cs ds : List Byte)
    (accFirst : s.locals "vacc01234567" = some (.halfwords
      (((List.zipWith (neonProduct p) as bs).map (fun x => ShiftISA.neonShift x p.shift)).map (neonFinish16 p))))
    (accSecond : s.locals "vacc89ABCDEF" = some (.halfwords
      (((List.zipWith (neonProduct p) cs ds).map (fun x => ShiftISA.neonShift x p.shift)).map (neonFinish16 p))))
    (lo : s.locals "voutput_min" = some (.vector 1 (List.replicate 16 p.outputMin)))
    (hi : s.locals "voutput_max" = some (.vector 1 (List.replicate 16 p.outputMax)))
    (ha : as.length = 8) (hb : bs.length = 8) (hc : cs.length = 8) (hd : ds.length = 8) :
    Exec cfg (takeStatements 3 (dropStatements 26 neonMainCode)) s
      (mainClampAfter s p as bs cs ds) := by
  have eq (aa bb : List Byte) : (((List.zipWith (neonProduct p) aa bb).map
      (fun x => ShiftISA.neonShift x p.shift)).map (neonFinish16 p)).map (clampHalf p) =
      List.zipWith (neonLane p) aa bb := by
    simp only [List.map_map, List.map_zipWith, Function.comp_def]
    change List.zipWith (fun a b => neonFinish p (ShiftISA.neonShift (neonProduct p a b) p.shift)) aa bb = _
    simp only [neonFinish_product]
  have h := main_clamp_raw_exec cfg s p _ _ accFirst accSecond lo hi
    (by simp [ha, hb]) (by simp [hc, hd])
  simpa only [List.map_append, eq] using h

end Salty.Kernels.QS8Add
