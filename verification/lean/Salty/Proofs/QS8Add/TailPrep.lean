import Salty.Proofs.QS8Add.NeonLanes

namespace Salty.Kernels.QS8Add
open CByte QuantizedAddISA
open SIMD.Arithmetic

def tailPrepAfter (s : State) (a b : Address) (p : Params) (as bs : List Byte) : State :=
  let t := tailLoadAfter s a b as bs
  let t := tailSubAfter t p as bs
  let t := tailMulAfter t p as
  let t := tailMlaAfter t p as bs
  let t := tailShiftAfter t p as bs
  let t := tailNarrowAfter t p as bs
  tailClampAfter t p as bs

set_option maxHeartbeats 1000000 in
theorem tail_prep_exec (cfg : Config) (s : State) (a b : Address) (p : Params) (as bs : List Byte)
    (params : NeonParams s p)
    (pa : s.locals "input_a" = some (.pointer a)) (pb : s.locals "input_b" = some (.pointer b))
    (ha : as.length = 8) (hb : bs.length = 8)
    (la : loadBytes s.memory a 8 = some as) (lb : loadBytes s.memory b 8 = some bs) :
    Exec cfg (takeStatements 16 neonTailBody) s (tailPrepAfter s a b p as bs) := by
  let s1 := tailLoadAfter s a b as bs
  let s2 := tailSubAfter s1 p as bs
  let s3 := tailMulAfter s2 p as
  let s4 := tailMlaAfter s3 p as bs
  let s5 := tailShiftAfter s4 p as bs
  let s6 := tailNarrowAfter s5 p as bs
  have load : Exec cfg (takeStatements 4 neonTailBody) s s1 := tail_load_exec cfg s a b as bs pa pb la lb
  have sub : Exec cfg (takeStatements 2 (dropStatements 4 neonTailBody)) s1 s2 :=
    tail_sub_exec cfg s1 p as bs
      (by simp [s1, tailLoadAfter, update]) (by simp [s1, tailLoadAfter, update])
      (by simp [s1, tailLoadAfter, update, params.zeroA])
      (by simp [s1, tailLoadAfter, update, params.zeroB]) ha hb
  have mul : Exec cfg (takeStatements 2 (dropStatements 6 neonTailBody)) s2 s3 :=
    tail_mul_exec cfg s2 p as
      (by simp [s2, tailSubAfter, update])
      (by simp [s2, s1, tailSubAfter, tailLoadAfter, update, params.multA]) ha
  have mla : Exec cfg (takeStatements 2 (dropStatements 8 neonTailBody)) s3 s4 :=
    tail_mla_exec cfg s3 p as bs
      (by simp [s3, tailMulAfter, update]) (by simp [s3, tailMulAfter, update])
      (by simp [s3, s2, tailMulAfter, tailSubAfter, update])
      (by simp [s3, s2, s1, tailMulAfter, tailSubAfter, tailLoadAfter, update, params.multB]) ha hb
  have shift : Exec cfg (takeStatements 2 (dropStatements 10 neonTailBody)) s4 s5 :=
    tail_shift_exec cfg s4 p as bs
      (by simp [s4, tailMlaAfter, update]) (by simp [s4, tailMlaAfter, update])
      (by simp [s4, s3, s2, s1, tailMlaAfter, tailMulAfter, tailSubAfter, tailLoadAfter, update, params.shift]) ha hb
  have narrow : Exec cfg (takeStatements 1 (dropStatements 12 neonTailBody)) s5 s6 :=
    tail_narrow_exec cfg s5 p as bs
      (by simp [s5, tailShiftAfter, update]) (by simp [s5, tailShiftAfter, update])
      (by simp [s5, s4, s3, s2, s1, tailShiftAfter, tailMlaAfter, tailMulAfter,
        tailSubAfter, tailLoadAfter, update, params.outputZero]) ha hb
  have clamp : Exec cfg (takeStatements 3 (dropStatements 13 neonTailBody)) s6 (tailPrepAfter s a b p as bs) :=
    tail_clamp_exec cfg s6 p as bs
      (by simp [s6, tailNarrowAfter, update])
      (by simp [s6, s5, s4, s3, s2, s1, tailNarrowAfter, tailShiftAfter, tailMlaAfter,
        tailMulAfter, tailSubAfter, tailLoadAfter, update, params.outputMin])
      (by simp [s6, s5, s4, s3, s2, s1, tailNarrowAfter, tailShiftAfter, tailMlaAfter,
        tailMulAfter, tailSubAfter, tailLoadAfter, update, params.outputMax]) ha hb
  exact exec_take_drop 4 load (exec_take_drop 2 sub (exec_take_drop 2 mul
    (exec_take_drop 2 mla (exec_take_drop 2 shift (exec_take_drop 1 narrow clamp)))))

theorem tailPrepAfter_params (s : State) (a b : Address) (p : Params) (as bs : List Byte)
    (h : NeonParams s p) : NeonParams (tailPrepAfter s a b p as bs) p := by
  constructor <;> simp [tailPrepAfter, tailClampAfter, tailNarrowAfter, tailShiftAfter,
    tailMlaAfter, tailMulAfter, tailSubAfter, tailLoadAfter, update,
    h.zeroA, h.zeroB, h.multA, h.multB, h.shift, h.outputZero, h.outputMin, h.outputMax]

end Salty.Kernels.QS8Add
