import Salty.Proofs.Rdsum.NeonMainSum

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

@[simp] theorem mainFold_length (kind : Interpretation) (m : Memory) (zero : Address) (increment count : Nat)
    (pointers : Nat → Address) (remaining : Int) (initial : Nat → List (BitVec 16)) (chunk : Nat)
    (len : (initial chunk).length = 8) :
    ((mainFold kind m zero increment count pointers remaining initial).acc chunk).length = 8 := by
  induction count generalizing pointers remaining initial with
  | zero => exact len
  | succ count ih =>
    apply ih
    exact rowAcc_length kind _ (initial chunk) 8 len (fun _ => readBytes_length ..) 7

theorem main_inner_word_frame (kind : Interpretation) (word : Nat) (within : word < 8) :
    (neonInnerLoop kind true).writes (neonWordName true word) = false := by
  have all : ∀ word : Fin 8, (neonInnerLoop kind true).writes (neonWordName true word.val) = false := by
    cases kind <;> decide
  exact all ⟨word,within⟩

theorem main_widen_row_frame (kind : Interpretation) (row : Nat) (within : row < 7) :
    (neonMainWiden kind).writes (rowName row) = false := by
  have all : ∀ row : Fin 7, (neonMainWiden kind).writes (rowName row.val) = false := by
    cases kind <;> decide
  exact all ⟨row,within⟩

/-- Complete main-path batch accumulation and widening, before r is reduced. -/
theorem neon_main_inner_widen_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero : Address) (stride first rows : Nat) (pointers : Nat → Address)
    (initial : Nat → BitVec 32) (positive : 0 < rows) (bounded : rows ≤ 252)
    (loc : NeonMainLocals kind s pointers zero rows (7*stride) zeroMainAcc)
    (words : ∀ word, word < neonWidth kind true/4 →
      s.locals (neonWordName true word) = some (.words32 (wordValues initial word)))
    (safe : GroupsSafe s.memory zero (mainReadSpan kind) (7*stride) ((rows+6)/7) pointers rows)
    (zeros : ∀ column, column < neonWidth kind true → s.memory.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < rows → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∃ t, Exec cfg (.seq (neonInnerLoop kind true) (neonMainWiden kind)) s t ∧ t.memory = s.memory ∧
      (∀ word, word < neonWidth kind true/4 → t.locals (neonWordName true word) =
        some (.words32 (wordValues (fun column => initial column+intervalSum kind s.memory input stride first rows column) word))) ∧
      (∀ i, i < 7 → t.locals (rowName i) = some (.pointer
        ((mainFold kind s.memory zero (7*stride) ((rows+6)/7) pointers rows zeroMainAcc).pointers i))) := by
  let result := mainFold kind s.memory zero (7*stride) ((rows+6)/7) pointers rows zeroMainAcc
  obtain ⟨u,loop,mem,uloc⟩ := neon_main_inner_total kind cfg s ((rows+6)/7) pointers zero rows (7*stride)
    zeroMainAcc (by intro j hj; simp [zeroMainAcc]) (group_count_ceiling rows) (by omega) loc safe
  have wordLoc : ∀ word, word < neonWidth kind true/4 → u.locals (neonWordName true word) = some (.words32 (wordValues initial word)) := by
    intro word hw
    have w8 : word < 8 := by cases kind <;> simp [neonWidth] at hw <;> omega
    exact (loop.locals_frame _ (main_inner_word_frame kind word w8)).trans (words word hw)
  let widened := mainWidenWord kind (wordValues initial) result.acc
  let t := mainWordsAfter u widened (neonWidth kind true/4)
  have wide : Exec cfg (neonMainWiden kind) u t := by
    rw [neon_main_widen_shape]
    exact main_widen_exec kind cfg u _ (by omega) (wordValues initial) result.acc
      (by intro word hw; simp [wordValues])
      (by intro chunk hc; exact mainFold_length kind s.memory zero (7*stride) ((rows+6)/7) pointers rows zeroMainAcc chunk (by simp [zeroMainAcc]))
      wordLoc uloc.acc
  refine ⟨t,.seq loop wide,?_,?_,?_⟩
  · exact (mainWordsAfter_memory ..).trans mem
  · intro word hw
    have w8 : neonWidth kind true/4 ≤ 8 := by cases kind <;> decide
    rw [mainWordsAfter_word u widened _ word w8 hw]
    congr 2
    apply widen_mainFold_word kind s.memory input zero stride ((rows+6)/7) first rows word pointers initial
      (group_count_ceiling rows) (by have := group_count_small rows bounded; omega) ?_ ptrs
    intro column hc
    apply zeros column
    cases kind <;> simp [neonWidth] at hw ⊢ <;> omega
  · intro i hi
    exact (wide.locals_frame _ (main_widen_row_frame kind i hi)).trans (uloc.rows i hi)

end Salty.Kernels.Rdsum
