import Salty.Proofs.QU8Add.NeonPrep
import Salty.Proofs.QU8Add.TailPrep
import Salty.Proofs.QU8Add.TailStores

namespace Salty.Kernels.QU8Add
open CByte QuantizedUAddISA
open SIMD.Unsigned

structure NeonLocals (s : State) (n : Nat) (a b output : Address) (p : Params) : Prop where
  params : NeonParams s p
  batch : s.locals "batch" = some (.integer n)
  inputA : s.locals "input_a" = some (.pointer a)
  inputB : s.locals "input_b" = some (.pointer b)
  outputPtr : s.locals "output" = some (.pointer output)

/-- Complete actual single padded source tail, including guarded4/2/1 stores. -/
theorem neon_tail_total (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (locals : NeonLocals s n a b output p) (short : n < 8)
    (safe : BinarySafe s.memory a b output n 7) :
    ∃ t, Exec cfg neonTail s t ∧ t.memory = binaryResult (neonLane p) s.memory a b output n := by
  by_cases zero : n = 0
  · subst n
    refine ⟨s, ?_, rfl⟩
    apply Exec.no (v := .integer 0)
    · simp [neonTail, firstStatement, dropStatements, Generated.QU8Add.neon,
        eval, binary, convert, Int.max_def, locals.batch]
    · rfl
    · exact .skip
  · let as := readBytes s.memory a 8
    let bs := readBytes s.memory b 8
    let prep := tailPrepAfter s a b p as bs
    have la : loadBytes s.memory a 8 = some as :=
      loadBytes_success _ _ _ (fun x hx => safe.readA x (footprint_mono (by omega) hx))
    have lb : loadBytes s.memory b 8 = some bs :=
      loadBytes_success _ _ _ (fun x hx => safe.readB x (footprint_mono (by omega) hx))
    have hp := tail_prep_exec cfg s a b p as bs locals.params locals.inputA locals.inputB
      (readBytes_length ..) (readBytes_length ..) la lb
    obtain ⟨t, hs, hm⟩ := neon_tail_stores cfg prep n output (List.zipWith (neonLane p) as bs)
      short (by simp [as, bs])
      (by simp [prep, tailPrepAfter, tailClampAfter, tailNarrowAfter, tailShiftAfter,
        tailMlaAfter, tailMulAfter, tailSubAfter, tailLoadAfter, update, locals.batch])
      (by simp [prep, tailPrepAfter, tailClampAfter, tailNarrowAfter, tailShiftAfter,
        tailMlaAfter, tailMulAfter, tailSubAfter, tailLoadAfter, update, locals.outputPtr])
      (by simp [prep, tailPrepAfter, tailClampAfter, update]) safe.writable
    refine ⟨t, ?_, ?_⟩
    · apply Exec.yes (v := .integer 1)
      · simp [neonTail, firstStatement, dropStatements, Generated.QU8Add.neon,
          eval, binary, convert, Int.max_def, locals.batch, zero]
      · rfl
      · exact .seq (exec_take_drop 14 hp hs) .skip
    · rw [hm]
      change writeBytes s.memory output ((List.zipWith (neonLane p) as bs).take n) = _
      simp only [List.take_zipWith, as, bs, readBytes_take _ _ n 8 (by omega), binaryResult, binaryBytes]

def main8StoreAfter (s : State) (output : Address) (m : Memory) : State :=
  update { s with memory := m } "output" (.pointer (output+8))

theorem main8_store_exec (cfg : Config) (s : State) (output : Address) (bs : List Byte) (m : Memory)
    (ptr : s.locals "output" = some (.pointer output))
    (vec : s.locals "vout01234567" = some (.vector 1 bs))
    (len : bs.length = 8) (store : storeBytes s.memory output bs = some m) :
    Exec cfg (dropStatements 16 neon8Code) s (main8StoreAfter s output m) := by
  have take : bs.take 8 = bs := by simp [← len]
  apply run_sound (fuel := 6)
  simp [neon8Code, neon8Body, neon8Loop, loopBody, firstStatement, dropStatements,
    Generated.QU8Add.neon, run, eval, effect, storeVector, update, ptr, vec, len, take,
    store, main8StoreAfter]

theorem main8PrepAfter_locals (s : State) (n : Nat) (a b output : Address) (p : Params)
    (as bs : List Byte) (h : NeonLocals s n a b output p) :
    NeonLocals (main8PrepAfter s a b p as bs) n (a+8) (b+8) output p := by
  refine ⟨main8PrepAfter_params _ _ _ _ _ _ h.params, ?_, ?_, ?_, ?_⟩ <;>
    simp [main8PrepAfter, main8ClampAfter, main8NarrowAfter, main8ShiftAfter, main8MlaAfter,
      main8MulAfter, main8SubAfter, main8LoadAfter, update, h.batch, h.outputPtr]

def main8After (s : State) (n : Nat) (a b output : Address) (p : Params)
    (as bs : List Byte) (m : Memory) : State :=
  update (main8StoreAfter (main8PrepAfter s a b p as bs) output m) "batch" (.integer (n-8 : Nat))

theorem main8_body_exec (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (as bs : List Byte) (m : Memory)
    (locals : NeonLocals s n a b output p) (large : 8 ≤ n) (bound : n < 2^64)
    (ha : as.length = 8) (hb : bs.length = 8)
    (la : loadBytes s.memory a 8 = some as) (lb : loadBytes s.memory b 8 = some bs)
    (store : storeBytes s.memory output (List.zipWith (neonLane p) as bs) = some m) :
    Exec cfg neon8Body s (main8After s n a b output p as bs m) := by
  let prep := main8PrepAfter s a b p as bs
  have hp := main8_prep_exec cfg s a b p as bs locals.params locals.inputA locals.inputB ha hb la lb
  have hl := main8PrepAfter_locals s n a b output p as bs locals
  have hs := main8_store_exec cfg prep output _ m hl.outputPtr
    (by simp [prep, main8PrepAfter, main8ClampAfter, update]) (by simp [ha, hb]) store
  have code : Exec cfg neon8Code s (main8StoreAfter prep output m) := exec_take_drop 16 hp hs
  have batch : prep.locals "batch" = some (.integer n) := hl.batch
  have c8 : convert .u64 8 = 8 := rfl
  have c1 : convert .u64 1 = 1 := rfl
  have sub : convert .u64 ((n : Int)-8) = (n-8 : Nat) := cast_sub n 8 large bound
  apply Exec.seq code
  apply Exec.assign
  simp [neon8Body, neon8Loop, loopBody, firstStatement, dropStatements, Generated.QU8Add.neon,
    eval, binary, main8StoreAfter, update, batch, c8, c1, sub]

theorem main8After_locals (s : State) (n : Nat) (a b output : Address) (p : Params)
    (as bs : List Byte) (m : Memory) (h : NeonLocals s n a b output p) :
    NeonLocals (main8After s n a b output p as bs m) (n-8) (a+8) (b+8) (output+8) p := by
  have h := main8PrepAfter_locals s n a b output p as bs h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> simp only [main8After, main8StoreAfter, update] <;>
      simp [h.params.zeroA, h.params.zeroB, h.params.multA, h.params.multB, h.params.shift,
        h.params.outputZero, h.params.outputMin, h.params.outputMax]
  all_goals simp [main8After, main8StoreAfter, update, h.inputA, h.inputB]

def neonMainAndTail : Stmt := dropStatements 13 Generated.QU8Add.neon

theorem neonMainAndTail_shape : neonMainAndTail = .seq neon8Loop (.seq neonTail .skip) := rfl

/-- Unbounded source8-byte loop with its actual guarded tail. -/
theorem neon_main_tail_total (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (locals : NeonLocals s n a b output p) (bound : n < 2^64)
    (safe : BinarySafe s.memory a b output n 7) :
    ∃ t, Exec cfg neonMainAndTail s t ∧ t.memory = binaryResult (neonLane p) s.memory a b output n := by
  by_cases small : n < 8
  · obtain ⟨t, tail, result⟩ := neon_tail_total cfg s n a b output p locals small safe
    refine ⟨t, ?_, result⟩
    rw [neonMainAndTail_shape]
    apply Exec.seq (t := s)
    · apply Exec.done (v := .integer 0)
      · simp [neon8Loop, firstStatement, dropStatements, Generated.QU8Add.neon,
          eval, binary, convert, Int.max_def, locals.batch, show ¬ (8 : Int) ≤ n by omega]
      · rfl
    · exact .seq tail .skip
  · have large : 8 ≤ n := by omega
    let as := readBytes s.memory a 8
    let bs := readBytes s.memory b 8
    let written := List.zipWith (neonLane p) as bs
    let m := writeBytes s.memory output written
    let next := main8After s n a b output p as bs m
    have len : written.length = 8 := by simp [written, as, bs]
    have la : loadBytes s.memory a 8 = some as :=
      loadBytes_success _ _ _ (fun x hx => safe.readA x (footprint_mono (by omega) hx))
    have lb : loadBytes s.memory b 8 = some bs :=
      loadBytes_success _ _ _ (fun x hx => safe.readB x (footprint_mono (by omega) hx))
    have store : storeBytes s.memory output written = some m :=
      storeBytes_success _ _ _ (fun x hx => safe.writable x (footprint_mono (by omega) hx))
    have body := main8_body_exec cfg s n a b output p as bs m locals large bound
      (readBytes_length ..) (readBytes_length ..) la lb store
    have nextlocals := main8After_locals s n a b output p as bs m locals
    obtain ⟨t, rest, result⟩ := neon_main_tail_total cfg next (n-8) (a+8) (b+8) (output+8)
      p nextlocals (by omega) (safe.advance large written)
    refine ⟨t, ?_, ?_⟩
    · rw [neonMainAndTail_shape] at rest ⊢
      cases rest with
      | seq loop tail =>
        apply Exec.seq (Exec.more (v := .integer 1) ?_ rfl body loop) tail
        simp [neon8Loop, firstStatement, dropStatements, Generated.QU8Add.neon,
          eval, binary, convert, Int.max_def, locals.batch, show (8 : Int) ≤ n by omega]
    · rw [result]
      exact (binaryResult_split (neonLane p) (safe.weaken_padding (by omega)) large).symm
termination_by n

end Salty.Kernels.QU8Add
