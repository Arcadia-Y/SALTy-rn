import Salty.Proofs.QS8Add.MainLanes
import Salty.Proofs.QS8Add.Tail

namespace Salty.Kernels.QS8Add
open CByte QuantizedAddISA
open SIMD.Arithmetic

def mainPrepAfter (s : State) (a b : Address) (p : Params) (as bs cs ds : List Byte) : State :=
  let s := mainFirstLoadAfter s a b as bs
  let s := mainSecondLoadAfter s (a+8) (b+8) cs ds
  let s := mainFirstSubAfter s p as bs
  let s := mainSecondSubAfter s p cs ds
  let s := mainFirstMulAfter s p as
  let s := mainSecondMulAfter s p cs
  let s := mainFirstMlaAfter s p as bs
  let s := mainSecondMlaAfter s p cs ds
  let s := mainFirstShiftAfter s p as bs
  let s := mainSecondShiftAfter s p cs ds
  let s := mainFirstNarrowAfter s p as bs
  let s := mainSecondNarrowAfter s p cs ds
  let s := mainClampAfter s p as bs cs ds
  s

set_option maxHeartbeats 2000000 in
theorem main_prep_exec (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (as bs cs ds : List Byte) (locals : NeonLocals s n a b output p)
    (ha : as.length = 8) (hb : bs.length = 8) (hc : cs.length = 8) (hd : ds.length = 8)
    (la : loadBytes s.memory a 8 = some as) (lb : loadBytes s.memory b 8 = some bs)
    (lc : loadBytes s.memory (a+8) 8 = some cs) (ld : loadBytes s.memory (b+8) 8 = some ds) :
    Exec cfg (takeStatements 29 neonMainCode) s (mainPrepAfter s a b p as bs cs ds) := by
  let s1 := mainFirstLoadAfter s a b as bs
  let s2 := mainSecondLoadAfter s1 (a+8) (b+8) cs ds
  let s3 := mainFirstSubAfter s2 p as bs
  let s4 := mainSecondSubAfter s3 p cs ds
  let s5 := mainFirstMulAfter s4 p as
  let s6 := mainSecondMulAfter s5 p cs
  let s7 := mainFirstMlaAfter s6 p as bs
  let s8 := mainSecondMlaAfter s7 p cs ds
  let s9 := mainFirstShiftAfter s8 p as bs
  let s10 := mainSecondShiftAfter s9 p cs ds
  let s11 := mainFirstNarrowAfter s10 p as bs
  let s12 := mainSecondNarrowAfter s11 p cs ds
  let s13 := mainClampAfter s12 p as bs cs ds
  have h1 : Exec cfg (takeStatements 4 (dropStatements 0 neonMainCode)) s s1 := by
    apply main_first_load_exec cfg s a b as bs
    all_goals simp [update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  have h2 : Exec cfg (takeStatements 4 (dropStatements 4 neonMainCode)) s1 s2 := by
    apply main_second_load_exec cfg s1 (a+8) (b+8) cs ds
    all_goals simp [s1, mainFirstLoadAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
    all_goals first | exact lc | exact ld
  have h3 : Exec cfg (takeStatements 2 (dropStatements 8 neonMainCode)) s2 s3 := by
    apply main_first_sub_exec cfg s2 p as bs
    all_goals simp [s1, s2, mainFirstLoadAfter, mainSecondLoadAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  have h4 : Exec cfg (takeStatements 2 (dropStatements 10 neonMainCode)) s3 s4 := by
    apply main_second_sub_exec cfg s3 p cs ds
    all_goals simp [s1, s2, s3, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  have h5 : Exec cfg (takeStatements 2 (dropStatements 12 neonMainCode)) s4 s5 := by
    apply main_first_mul_exec cfg s4 p as
    all_goals simp [s1, s2, s3, s4, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, mainSecondSubAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  have h6 : Exec cfg (takeStatements 2 (dropStatements 14 neonMainCode)) s5 s6 := by
    apply main_second_mul_exec cfg s5 p cs
    all_goals simp [s1, s2, s3, s4, s5, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, mainSecondSubAfter, mainFirstMulAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  have h7 : Exec cfg (takeStatements 2 (dropStatements 16 neonMainCode)) s6 s7 := by
    apply main_first_mla_exec cfg s6 p as bs
    all_goals simp [s1, s2, s3, s4, s5, s6, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, mainSecondSubAfter, mainFirstMulAfter, mainSecondMulAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  have h8 : Exec cfg (takeStatements 2 (dropStatements 18 neonMainCode)) s7 s8 := by
    apply main_second_mla_exec cfg s7 p cs ds
    all_goals simp [s1, s2, s3, s4, s5, s6, s7, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, mainSecondSubAfter, mainFirstMulAfter, mainSecondMulAfter, mainFirstMlaAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  have h9 : Exec cfg (takeStatements 2 (dropStatements 20 neonMainCode)) s8 s9 := by
    apply main_first_shift_exec cfg s8 p as bs
    all_goals simp [s1, s2, s3, s4, s5, s6, s7, s8, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, mainSecondSubAfter, mainFirstMulAfter, mainSecondMulAfter, mainFirstMlaAfter, mainSecondMlaAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  have h10 : Exec cfg (takeStatements 2 (dropStatements 22 neonMainCode)) s9 s10 := by
    apply main_second_shift_exec cfg s9 p cs ds
    all_goals simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, mainSecondSubAfter, mainFirstMulAfter, mainSecondMulAfter, mainFirstMlaAfter, mainSecondMlaAfter, mainFirstShiftAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  have h11 : Exec cfg (takeStatements 1 (dropStatements 24 neonMainCode)) s10 s11 := by
    apply main_first_narrow_exec cfg s10 p as bs
    all_goals simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, mainSecondSubAfter, mainFirstMulAfter, mainSecondMulAfter, mainFirstMlaAfter, mainSecondMlaAfter, mainFirstShiftAfter, mainSecondShiftAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  have h12 : Exec cfg (takeStatements 1 (dropStatements 25 neonMainCode)) s11 s12 := by
    apply main_second_narrow_exec cfg s11 p cs ds
    all_goals simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, mainSecondSubAfter, mainFirstMulAfter, mainSecondMulAfter, mainFirstMlaAfter, mainSecondMlaAfter, mainFirstShiftAfter, mainSecondShiftAfter, mainFirstNarrowAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  have h13 : Exec cfg (takeStatements 3 (dropStatements 26 neonMainCode)) s12 s13 := by
    apply main_clamp_exec cfg s12 p as bs cs ds
    all_goals simp [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, mainSecondSubAfter, mainFirstMulAfter, mainSecondMulAfter, mainFirstMlaAfter, mainSecondMlaAfter, mainFirstShiftAfter, mainSecondShiftAfter, mainFirstNarrowAfter, mainSecondNarrowAfter, update, locals.inputA, locals.inputB, locals.params.zeroA, locals.params.zeroB, locals.params.multA, locals.params.multB, locals.params.shift, locals.params.outputZero, locals.params.outputMin, locals.params.outputMax, ha, hb, hc, hd, la, lb, lc, ld]
  exact (exec_take_drop 4 h1 (exec_take_drop 4 h2 (exec_take_drop 2 h3 (exec_take_drop 2 h4 (exec_take_drop 2 h5 (exec_take_drop 2 h6 (exec_take_drop 2 h7 (exec_take_drop 2 h8 (exec_take_drop 2 h9 (exec_take_drop 2 h10 (exec_take_drop 1 h11 (exec_take_drop 1 h12 h13))))))))))))

theorem mainPrepAfter_locals (s : State) (n : Nat) (a b output : Address) (p : Params)
    (as bs cs ds : List Byte) (h : NeonLocals s n a b output p) :
    NeonLocals (mainPrepAfter s a b p as bs cs ds) n (a+16) (b+16) output p := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    all_goals simp [mainPrepAfter, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, mainSecondSubAfter, mainFirstMulAfter, mainSecondMulAfter, mainFirstMlaAfter, mainSecondMlaAfter, mainFirstShiftAfter, mainSecondShiftAfter, mainFirstNarrowAfter, mainSecondNarrowAfter, mainClampAfter, update, h.params.zeroA, h.params.zeroB, h.params.multA, h.params.multB, h.params.shift, h.params.outputZero, h.params.outputMin, h.params.outputMax, h.batch, h.outputPtr, BitVec.add_assoc]
  all_goals simp [mainPrepAfter, mainFirstLoadAfter, mainSecondLoadAfter, mainFirstSubAfter, mainSecondSubAfter, mainFirstMulAfter, mainSecondMulAfter, mainFirstMlaAfter, mainSecondMlaAfter, mainFirstShiftAfter, mainSecondShiftAfter, mainFirstNarrowAfter, mainSecondNarrowAfter, mainClampAfter, update, h.params.zeroA, h.params.zeroB, h.params.multA, h.params.multB, h.params.shift, h.params.outputZero, h.params.outputMin, h.params.outputMax, h.batch, h.outputPtr, BitVec.add_assoc]

end Salty.Kernels.QS8Add
