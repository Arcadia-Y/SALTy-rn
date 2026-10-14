import Salty.Proofs.QS8Add.TailPrep
import Salty.Proofs.QS8Add.TailStores

namespace Salty.Kernels.QS8Add
open CByte QuantizedAddISA
open SIMD.Arithmetic

structure NeonLocals (s : State) (n : Nat) (a b output : Address) (p : Params) : Prop where
  params : NeonParams s p
  batch : s.locals "batch" = some (.integer n)
  inputA : s.locals "input_a" = some (.pointer a)
  inputB : s.locals "input_b" = some (.pointer b)
  outputPtr : s.locals "output" = some (.pointer output)

def tailStoreBranch : Stmt := firstStatement (dropStatements 16 neonTailBody)
def tailFullStores : Stmt := branchYes tailStoreBranch
def tailShortStores : Stmt := match tailStoreBranch with
  | .branch _ _ no => no
  | _ => .skip

def tailFullAfter (s : State) (n : Nat) (output : Address) (m : Memory) : State :=
  update (update { s with memory := m } "output" (.pointer (output + 8)))
    "batch" (.integer (n - 8 : Nat))

theorem tail_full_stores_exec (cfg : Config) (s : State) (n : Nat) (output : Address)
    (bs : List Byte) (m : Memory) (large : 8 ≤ n) (bound : n < 2^64)
    (batch : s.locals "batch" = some (.integer n))
    (ptr : s.locals "output" = some (.pointer output))
    (vec : s.locals "vout01234567" = some (.vector 1 bs))
    (len : bs.length = 8) (store : storeBytes s.memory output bs = some m) :
    Exec cfg tailFullStores s (tailFullAfter s n output m) := by
  have take : bs.take 8 = bs := by simp [← len]
  have c8 : convert .u64 8 = 8 := rfl
  have c1 : convert .u64 1 = 1 := rfl
  have sub : convert .u64 ((n : Int) - 8) = (n-8 : Nat) := cast_sub n 8 large bound
  apply run_sound (fuel := 8)
  simp [tailFullStores, tailStoreBranch, branchYes, neonTailBody, neonTail,
    firstStatement, dropStatements, Generated.QS8Add.neon, run, eval, effect, storeVector,
    binary, update, ptr, vec, batch, len, take, store, c8, c1, sub,
    tailFullAfter]

theorem tail_short_stores_exec (cfg : Config) (s : State) (n : Nat) (output : Address)
    (bs : List Byte) (short : n < 8) (len : bs.length = 8)
    (batch : s.locals "batch" = some (.integer n))
    (ptr : s.locals "output" = some (.pointer output))
    (vec : s.locals "vout01234567" = some (.vector 1 bs))
    (safe : ∀ a, Footprint output n a → s.memory.writable a = true) :
    ∃ t, Exec cfg tailShortStores s t ∧
      t.memory = writeBytes s.memory output (bs.take n) ∧
      t.locals "batch" = some (.integer 0) := by
  obtain ⟨t, ht, hm⟩ := neon_tail_stores cfg s n output bs short len batch ptr vec safe
  refine ⟨update t "batch" (.integer 0), ?_, hm, ?_⟩
  · apply exec_take_drop 3 ht
    exact .seq (.assign (by simp [eval, convert, Int.max_def])) .skip
  · simp [update]

theorem tailPrepAfter_locals (s : State) (n : Nat) (a b output : Address) (p : Params)
    (as bs : List Byte) (h : NeonLocals s n a b output p) :
    NeonLocals (tailPrepAfter s a b p as bs) n (a + 8) (b + 8) output p := by
  refine ⟨tailPrepAfter_params _ _ _ _ _ _ h.params, ?_, ?_, ?_, ?_⟩ <;>
    simp [tailPrepAfter, tailClampAfter, tailNarrowAfter, tailShiftAfter, tailMlaAfter,
      tailMulAfter, tailSubAfter, tailLoadAfter, update, h.batch, h.outputPtr]

theorem tailFullAfter_locals (s : State) (n : Nat) (a b output : Address) (p : Params)
    (m : Memory) (h : NeonLocals s n a b output p) :
    NeonLocals (tailFullAfter s n output m) (n-8) a b (output+8) p := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> simp [tailFullAfter, update, h.params.zeroA, h.params.zeroB,
      h.params.multA, h.params.multB, h.params.shift, h.params.outputZero,
      h.params.outputMin, h.params.outputMax]
  all_goals simp [tailFullAfter, update, h.inputA, h.inputB]

/-- One full eight-byte iteration of the actual NEON do/while tail. -/
theorem neon_tail_full_body (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (locals : NeonLocals s n a b output p) (large : 8 ≤ n) (bound : n < 2^64)
    (safe : BinarySafe s.memory a b output n 7) :
    ∃ t, Exec cfg neonTailBody s t ∧
      t.memory = binaryResult (neonLane p) s.memory a b output 8 ∧
      NeonLocals t (n-8) (a+8) (b+8) (output+8) p := by
  let as := readBytes s.memory a 8
  let bs := readBytes s.memory b 8
  let prep := tailPrepAfter s a b p as bs
  let written := List.zipWith (neonLane p) as bs
  let m := writeBytes s.memory output written
  have la : loadBytes s.memory a 8 = some as :=
    loadBytes_success _ _ _ (fun x hx => safe.readA x (footprint_mono (by omega) hx))
  have lb : loadBytes s.memory b 8 = some bs :=
    loadBytes_success _ _ _ (fun x hx => safe.readB x (footprint_mono (by omega) hx))
  have hp := tail_prep_exec cfg s a b p as bs locals.params locals.inputA locals.inputB
    (readBytes_length ..) (readBytes_length ..) la lb
  have hl := tailPrepAfter_locals s n a b output p as bs locals
  have len : written.length = 8 := by simp [written, as, bs]
  have hs : storeBytes prep.memory output written = some m :=
    storeBytes_success _ _ _ (fun x hx => safe.writable x (footprint_mono (by omega) hx))
  have stores := tail_full_stores_exec cfg prep n output written m large bound hl.batch hl.outputPtr
    (by simp [prep, tailPrepAfter, tailClampAfter, update, written]) len hs
  refine ⟨tailFullAfter prep n output m, ?_, rfl, tailFullAfter_locals _ _ _ _ _ _ _ hl⟩
  apply exec_take_drop 16 hp
  apply Exec.seq _ .skip
  apply Exec.yes (v := .integer 1)
  · simp [tailStoreBranch, firstStatement, dropStatements, neonTailBody, neonTail,
      branchYes, Generated.QS8Add.neon, eval, binary, convert, Int.max_def, hl.batch,
      show (8 : Int) ≤ n by omega]
  · rfl
  · exact stores

/-- The short iteration writes only the requested prefix of its padded loads. -/
theorem neon_tail_short_body (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (locals : NeonLocals s n a b output p) (pos : 0 < n) (short : n < 8)
    (safe : BinarySafe s.memory a b output n 7) :
    ∃ t, Exec cfg neonTailBody s t ∧
      t.memory = binaryResult (neonLane p) s.memory a b output n ∧
      t.locals "batch" = some (.integer 0) := by
  let as := readBytes s.memory a 8
  let bs := readBytes s.memory b 8
  let prep := tailPrepAfter s a b p as bs
  have la : loadBytes s.memory a 8 = some as :=
    loadBytes_success _ _ _ (fun x hx => safe.readA x (footprint_mono (by omega) hx))
  have lb : loadBytes s.memory b 8 = some bs :=
    loadBytes_success _ _ _ (fun x hx => safe.readB x (footprint_mono (by omega) hx))
  have hp := tail_prep_exec cfg s a b p as bs locals.params locals.inputA locals.inputB
    (readBytes_length ..) (readBytes_length ..) la lb
  have hl := tailPrepAfter_locals s n a b output p as bs locals
  obtain ⟨t, ht, hm, hb⟩ := tail_short_stores_exec cfg prep n output
    (List.zipWith (neonLane p) as bs) short (by simp [as, bs]) hl.batch hl.outputPtr
    (by simp [prep, tailPrepAfter, tailClampAfter, update]) safe.writable
  refine ⟨t, ?_, ?_, hb⟩
  · apply exec_take_drop 16 hp
    apply Exec.seq _ .skip
    apply Exec.no (v := .integer 0)
    · simp [tailStoreBranch, firstStatement, dropStatements, neonTailBody, neonTail,
        branchYes, Generated.QS8Add.neon, eval, binary, convert, Int.max_def, hl.batch,
        show ¬ (8 : Int) ≤ n by omega]
    · rfl
    · exact ht
  · rw [hm]
    change writeBytes s.memory output ((List.zipWith (neonLane p) as bs).take n) = _
    simp only [List.take_zipWith, as, bs, readBytes_take _ _ n 8 (by omega),
      binaryResult, binaryBytes]

def tailCondition : Expr := .bin .ne (.var "batch") (.cast .u64 (.lit 0))
def neonTailLoop : Stmt := .loop tailCondition neonTailBody

/-- Syntactic equality includes the source do/while's mandatory first body. -/
theorem neonTail_shape : neonTail = .branch tailCondition
    (.seq (.seq neonTailBody neonTailLoop) .skip) .skip := rfl

theorem tail_condition_zero (cfg : Config) (s : State)
    (h : s.locals "batch" = some (.integer 0)) :
    eval cfg s tailCondition = some (.integer 0) := by
  simp [tailCondition, eval, binary, convert, Int.max_def, h]

theorem tail_condition_positive (cfg : Config) (s : State) (n : Nat) (pos : 0 < n)
    (h : s.locals "batch" = some (.integer n)) :
    eval cfg s tailCondition = some (.integer 1) := by
  simp [tailCondition, eval, binary, convert, Int.max_def, h, show n ≠ 0 by omega]

/-- Unbounded termination and complete memory result for the source tail loop. -/
theorem neon_tail_loop_total (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (locals : NeonLocals s n a b output p) (bound : n < 2^64)
    (safe : BinarySafe s.memory a b output n 7) :
    ∃ t, Exec cfg neonTailLoop s t ∧
      t.memory = binaryResult (neonLane p) s.memory a b output n := by
  by_cases zero : n = 0
  · subst n
    exact ⟨s, .done (tail_condition_zero cfg s (by simpa using locals.batch)) rfl, rfl⟩
  · have cond := tail_condition_positive cfg s n (by omega) locals.batch
    by_cases large : 8 ≤ n
    · obtain ⟨next, body, memory, nextlocals⟩ :=
        neon_tail_full_body cfg s n a b output p locals large bound safe
      have nextsafe : BinarySafe next.memory (a+8) (b+8) (output+8) (n-8) 7 := by
        rw [memory]
        exact safe.advance large (binaryBytes (neonLane p) s.memory a b 8)
      obtain ⟨t, rest, result⟩ := neon_tail_loop_total cfg next (n-8) (a+8) (b+8)
        (output+8) p nextlocals (by omega) nextsafe
      refine ⟨t, .more cond rfl body rest, ?_⟩
      rw [result, memory]
      exact (binaryResult_split (neonLane p) (safe.weaken_padding (by omega)) large).symm
    · obtain ⟨t, body, memory, batch⟩ :=
        neon_tail_short_body cfg s n a b output p locals (by omega) (by omega) safe
      exact ⟨t, .more cond rfl body (.done (tail_condition_zero cfg t batch) rfl), memory⟩
termination_by n

/-- Complete extracted NEON tail, including its outer guard and do/while. -/
theorem neon_tail_total (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (locals : NeonLocals s n a b output p) (bound : n < 2^64)
    (safe : BinarySafe s.memory a b output n 7) :
    ∃ t, Exec cfg neonTail s t ∧
      t.memory = binaryResult (neonLane p) s.memory a b output n := by
  rw [neonTail_shape]
  by_cases zero : n = 0
  · subst n
    exact ⟨s, .no (tail_condition_zero cfg s (by simpa using locals.batch)) rfl .skip, rfl⟩
  · obtain ⟨t, ht, hm⟩ := neon_tail_loop_total cfg s n a b output p locals bound safe
    have cond := tail_condition_positive cfg s n (by omega) locals.batch
    refine ⟨t, .yes cond rfl ?_, hm⟩
    cases ht with
    | done he hf => simp [cond] at he; subst_vars; contradiction
    | more he hf hb hr => exact .seq (.seq hb hr) .skip

end Salty.Kernels.QS8Add
