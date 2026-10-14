import Salty.Proofs.QU8Add.NeonLanes

namespace Salty.Kernels.QU8Add
open CByte QuantizedUAddISA
open SIMD.Unsigned

def main8PrepAfter (s : State) (a b : Address) (p : Params) (as bs : List Byte) : State :=
  let t := main8LoadAfter s a b as bs
  let t := main8SubAfter t p as bs
  let t := main8MulAfter t p as
  let t := main8MlaAfter t p as bs
  let t := main8ShiftAfter t p as bs
  let t := main8NarrowAfter t p as bs
  main8ClampAfter t p as bs

set_option maxHeartbeats 1000000 in
theorem main8_prep_exec (cfg : Config) (s : State) (a b : Address) (p : Params) (as bs : List Byte)
    (params : NeonParams s p)
    (pa : s.locals "input_a" = some (.pointer a)) (pb : s.locals "input_b" = some (.pointer b))
    (ha : as.length = 8) (hb : bs.length = 8)
    (la : loadBytes s.memory a 8 = some as) (lb : loadBytes s.memory b 8 = some bs) :
    Exec cfg (takeStatements 16 neon8Code) s (main8PrepAfter s a b p as bs) := by
  let s1 := main8LoadAfter s a b as bs
  let s2 := main8SubAfter s1 p as bs
  let s3 := main8MulAfter s2 p as
  let s4 := main8MlaAfter s3 p as bs
  let s5 := main8ShiftAfter s4 p as bs
  let s6 := main8NarrowAfter s5 p as bs
  have load : Exec cfg (takeStatements 4 neon8Code) s s1 := main8_load_exec cfg s a b as bs pa pb la lb
  have sub : Exec cfg (takeStatements 2 (dropStatements 4 neon8Code)) s1 s2 :=
    main8_sub_exec cfg s1 p as bs
      (by simp [s1, main8LoadAfter, update]) (by simp [s1, main8LoadAfter, update])
      (by simp [s1, main8LoadAfter, update, params.zeroA])
      (by simp [s1, main8LoadAfter, update, params.zeroB]) ha hb
  have mul : Exec cfg (takeStatements 2 (dropStatements 6 neon8Code)) s2 s3 :=
    main8_mul_exec cfg s2 p as
      (by simp [s2, main8SubAfter, update])
      (by simp [s2, s1, main8SubAfter, main8LoadAfter, update, params.multA]) ha
  have mla : Exec cfg (takeStatements 2 (dropStatements 8 neon8Code)) s3 s4 :=
    main8_mla_exec cfg s3 p as bs
      (by simp [s3, main8MulAfter, update]) (by simp [s3, main8MulAfter, update])
      (by simp [s3, s2, main8MulAfter, main8SubAfter, update])
      (by simp [s3, s2, s1, main8MulAfter, main8SubAfter, main8LoadAfter, update, params.multB]) ha hb
  have shift : Exec cfg (takeStatements 2 (dropStatements 10 neon8Code)) s4 s5 :=
    main8_shift_exec cfg s4 p as bs
      (by simp [s4, main8MlaAfter, update]) (by simp [s4, main8MlaAfter, update])
      (by simp [s4, s3, s2, s1, main8MlaAfter, main8MulAfter, main8SubAfter, main8LoadAfter, update, params.shift]) ha hb
  have narrow : Exec cfg (takeStatements 1 (dropStatements 12 neon8Code)) s5 s6 :=
    main8_narrow_exec cfg s5 p as bs
      (by simp [s5, main8ShiftAfter, update]) (by simp [s5, main8ShiftAfter, update])
      (by simp [s5, s4, s3, s2, s1, main8ShiftAfter, main8MlaAfter, main8MulAfter,
        main8SubAfter, main8LoadAfter, update, params.outputZero]) ha hb
  have clamp : Exec cfg (takeStatements 3 (dropStatements 13 neon8Code)) s6 (main8PrepAfter s a b p as bs) :=
    main8_clamp_exec cfg s6 p as bs
      (by simp [s6, main8NarrowAfter, update])
      (by simp [s6, s5, s4, s3, s2, s1, main8NarrowAfter, main8ShiftAfter, main8MlaAfter,
        main8MulAfter, main8SubAfter, main8LoadAfter, update, params.outputMin])
      (by simp [s6, s5, s4, s3, s2, s1, main8NarrowAfter, main8ShiftAfter, main8MlaAfter,
        main8MulAfter, main8SubAfter, main8LoadAfter, update, params.outputMax]) ha hb
  exact exec_take_drop 4 load (exec_take_drop 2 sub (exec_take_drop 2 mul
    (exec_take_drop 2 mla (exec_take_drop 2 shift (exec_take_drop 1 narrow clamp)))))

theorem main8PrepAfter_params (s : State) (a b : Address) (p : Params) (as bs : List Byte)
    (h : NeonParams s p) : NeonParams (main8PrepAfter s a b p as bs) p := by
  constructor <;> simp [main8PrepAfter, main8ClampAfter, main8NarrowAfter, main8ShiftAfter,
    main8MlaAfter, main8MulAfter, main8SubAfter, main8LoadAfter, update,
    h.zeroA, h.zeroB, h.multA, h.multB, h.shift, h.outputZero, h.outputMin, h.outputMax]

end Salty.Kernels.QU8Add
