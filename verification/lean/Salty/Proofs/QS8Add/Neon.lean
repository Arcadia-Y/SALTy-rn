import Salty.Proofs.QS8Add.MainPrep

namespace Salty.Kernels.QS8Add
open CByte QuantizedAddISA
open SIMD.Arithmetic

def mainStoreAfter (s : State) (output : Address) (m : Memory) : State :=
  update { s with memory := m } "output" (.pointer (output+16))

theorem main_store_exec (cfg : Config) (s : State) (output : Address)
    (bs : List Byte) (m : Memory)
    (ptr : s.locals "output" = some (.pointer output))
    (vec : s.locals "vout0123456789ABCDEF" = some (.vector 1 bs))
    (len : bs.length = 16) (store : storeBytes s.memory output bs = some m) :
    Exec cfg (dropStatements 29 neonMainCode) s (mainStoreAfter s output m) := by
  have take : bs.take 16 = bs := by simp [← len]
  apply run_sound (fuel := 6)
  simp [neonMainCode, neonMainBody, neonMainLoop, loopBody, firstStatement,
    dropStatements, Generated.QS8Add.neon, run, eval, effect, storeVector,
    update, ptr, vec, len, take, store, mainStoreAfter]

def mainAfter (s : State) (n : Nat) (a b output : Address) (p : Params)
    (as bs cs ds : List Byte) (m : Memory) : State :=
  update (mainStoreAfter (mainPrepAfter s a b p as bs cs ds) output m)
    "batch" (.integer (n-16 : Nat))

theorem main_body_exec (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (as bs cs ds : List Byte) (m : Memory)
    (locals : NeonLocals s n a b output p) (large : 16 ≤ n) (bound : n < 2^64)
    (ha : as.length = 8) (hb : bs.length = 8) (hc : cs.length = 8) (hd : ds.length = 8)
    (la : loadBytes s.memory a 8 = some as) (lb : loadBytes s.memory b 8 = some bs)
    (lc : loadBytes s.memory (a+8) 8 = some cs) (ld : loadBytes s.memory (b+8) 8 = some ds)
    (store : storeBytes s.memory output
      (List.zipWith (neonLane p) as bs ++ List.zipWith (neonLane p) cs ds) = some m) :
    Exec cfg neonMainBody s (mainAfter s n a b output p as bs cs ds m) := by
  let prep := mainPrepAfter s a b p as bs cs ds
  have hp := main_prep_exec cfg s n a b output p as bs cs ds locals ha hb hc hd la lb lc ld
  have hl := mainPrepAfter_locals s n a b output p as bs cs ds locals
  have hs := main_store_exec cfg prep output _ m hl.outputPtr
    (by simp [prep, mainPrepAfter, mainClampAfter, update]) (by simp [ha, hb, hc, hd]) store
  have code : Exec cfg neonMainCode s (mainStoreAfter prep output m) := exec_take_drop 29 hp hs
  have batch : prep.locals "batch" = some (.integer n) := hl.batch
  have c16 : convert .u64 16 = 16 := rfl
  have c1 : convert .u64 1 = 1 := rfl
  have sub : convert .u64 ((n : Int)-16) = (n-16 : Nat) := cast_sub n 16 large bound
  apply Exec.seq code
  apply Exec.assign
  simp [neonMainBody, neonMainLoop, loopBody, firstStatement, dropStatements,
    Generated.QS8Add.neon, eval, binary, mainStoreAfter, update, batch, c16, c1, sub]

theorem mainAfter_locals (s : State) (n : Nat) (a b output : Address) (p : Params)
    (as bs cs ds : List Byte) (m : Memory) (h : NeonLocals s n a b output p) :
    NeonLocals (mainAfter s n a b output p as bs cs ds m) (n-16) (a+16) (b+16) (output+16) p := by
  have h := mainPrepAfter_locals s n a b output p as bs cs ds h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> simp only [mainAfter, mainStoreAfter, update] <;>
      simp [h.params.zeroA, h.params.zeroB, h.params.multA, h.params.multB, h.params.shift,
        h.params.outputZero, h.params.outputMin, h.params.outputMax]
  all_goals simp [mainAfter, mainStoreAfter, update, h.inputA, h.inputB]

set_option maxHeartbeats 1000000 in
theorem neon_main_body_total (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (locals : NeonLocals s n a b output p) (large : 16 ≤ n) (bound : n < 2^64)
    (safe : BinarySafe s.memory a b output n 7) :
    ∃ t, Exec cfg neonMainBody s t ∧
      t.memory = binaryResult (neonLane p) s.memory a b output 16 ∧
      NeonLocals t (n-16) (a+16) (b+16) (output+16) p := by
  let as := readBytes s.memory a 8
  let bs := readBytes s.memory b 8
  let cs := readBytes s.memory (a+8) 8
  let ds := readBytes s.memory (b+8) 8
  let written := List.zipWith (neonLane p) as bs ++ List.zipWith (neonLane p) cs ds
  let m := writeBytes s.memory output written
  have la : loadBytes s.memory a 8 = some as :=
    loadBytes_success _ _ _ (fun x hx => safe.readA x (footprint_mono (by omega) hx))
  have lb : loadBytes s.memory b 8 = some bs :=
    loadBytes_success _ _ _ (fun x hx => safe.readB x (footprint_mono (by omega) hx))
  have lc : loadBytes s.memory (a+8) 8 = some cs :=
    loadBytes_success _ _ _ (fun x hx => safe.readA x (footprint_shift_within (start := 8) (by omega) hx))
  have ld : loadBytes s.memory (b+8) 8 = some ds :=
    loadBytes_success _ _ _ (fun x hx => safe.readB x (footprint_shift_within (start := 8) (by omega) hx))
  have len : written.length = 16 := by simp [written, as, bs, cs, ds]
  have store : storeBytes s.memory output written = some m :=
    storeBytes_success _ _ _ (fun x hx => safe.writable x (footprint_mono (by omega) hx))
  refine ⟨mainAfter s n a b output p as bs cs ds m,
    main_body_exec cfg s n a b output p as bs cs ds m locals large bound
      (readBytes_length ..) (readBytes_length ..) (readBytes_length ..) (readBytes_length ..)
      la lb lc ld store, ?_, mainAfter_locals _ _ _ _ _ _ _ _ _ _ _ locals⟩
  change m = binaryResult (neonLane p) s.memory a b output (8+8)
  rw [binaryResult, binaryBytes_add (neonLane p) s.memory a b 8 8]
  rfl

def neonMainAndTail : Stmt := dropStatements 13 Generated.QS8Add.neon

theorem neonMainAndTail_shape : neonMainAndTail = .seq neonMainLoop (.seq neonTail .skip) := rfl

/-- Complete extracted 16-byte loop and guarded do/while tail, for every length.
All reads refer to both original input arrays and all other memory is framed. -/
theorem neon_main_tail_total (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (locals : NeonLocals s n a b output p) (bound : n < 2^64)
    (safe : BinarySafe s.memory a b output n 7) :
    ∃ t, Exec cfg neonMainAndTail s t ∧
      t.memory = binaryResult (neonLane p) s.memory a b output n := by
  by_cases small : n < 16
  · obtain ⟨t, tail, result⟩ := neon_tail_total cfg s n a b output p locals bound safe
    refine ⟨t, ?_, result⟩
    rw [neonMainAndTail_shape]
    apply Exec.seq (t := s)
    · apply Exec.done (v := .integer 0)
      · simp [neonMainLoop, firstStatement, dropStatements, Generated.QS8Add.neon,
          eval, binary, convert, Int.max_def, locals.batch, show ¬ (16 : Int) ≤ n by omega]
      · rfl
    · exact .seq tail .skip
  · have large : 16 ≤ n := by omega
    obtain ⟨next, body, memory, nextlocals⟩ := neon_main_body_total cfg s n a b output p locals large bound safe
    have nextsafe : BinarySafe next.memory (a+16) (b+16) (output+16) (n-16) 7 := by
      rw [memory]
      exact safe.advance large (binaryBytes (neonLane p) s.memory a b 16)
    obtain ⟨t, rest, result⟩ := neon_main_tail_total cfg next (n-16) (a+16) (b+16) (output+16)
      p nextlocals (by omega) nextsafe
    refine ⟨t, ?_, ?_⟩
    · rw [neonMainAndTail_shape] at rest ⊢
      cases rest with
      | seq loop tail =>
        apply Exec.seq (Exec.more (v := .integer 1) ?_ rfl body loop) tail
        simp [neonMainLoop, firstStatement, dropStatements, Generated.QS8Add.neon,
          eval, binary, convert, Int.max_def, locals.batch, show (16 : Int) ≤ n by omega]
    · rw [result, memory]
      exact (binaryResult_split (neonLane p) (safe.weaken_padding (by omega)) large).symm
termination_by n

end Salty.Kernels.QS8Add
