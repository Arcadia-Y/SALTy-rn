import Salty.Proofs.Rdsum.NeonMainSchedule

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

private theorem word_name_injective : ∀ (i j : Fin 8),
    neonWordName true i.val = neonWordName true j.val → i = j := by decide

private theorem word_name_ne (i j : Nat) (hi : i < 8) (hj : j < 8) (ne : i ≠ j) :
    neonWordName true i ≠ neonWordName true j := by
  intro h
  have eq := word_name_injective ⟨i,hi⟩ ⟨j,hj⟩ h
  exact ne (congrArg Fin.val eq)

private theorem word_half_ne (kind : Interpretation) (i j : Nat) (hi : i < 8) (hj : j < 4) :
    neonHalfName kind true j ≠ neonWordName true i := by
  have all : ∀ (i : Fin 8) (j : Fin 4), neonHalfName kind true j.val ≠ neonWordName true i.val := by
    cases kind <;> decide
  exact all ⟨i,hi⟩ ⟨j,hj⟩

def mainWidenWord (kind : Interpretation) (initial : Nat → List (BitVec 32))
    (half : Nat → List (BitVec 16)) (word : Nat) : List (BitVec 32) :=
  WideningISA.widenAdd32 kind (initial word)
    (if word % 2 = 0 then (half (word/2)).take 4 else (half (word/2)).drop 4)

def mainWidenWordCode (kind : Interpretation) (word : Nat) : Stmt :=
  .assign (neonWordName true word) (.call (rowHalfPrim kind)
    [.var (neonWordName true word), .call (if word % 2 = 0 then .lowI16x4 else .highI16x4)
      [.var (neonHalfName kind true (word/2))]])

def mainWidenCode (kind : Interpretation) : Nat → Stmt
  | 0 => .skip
  | n+1 => appendStatements (mainWidenCode kind n) (.seq (mainWidenWordCode kind n) .skip)

def mainWordsAfter (s : State) (words : Nat → List (BitVec 32)) : Nat → State
  | 0 => s
  | n+1 => update (mainWordsAfter s words n) (neonWordName true n) (.words32 (words n))

@[simp] theorem mainWordsAfter_memory (s : State) (words : Nat → List (BitVec 32)) (n : Nat) :
    (mainWordsAfter s words n).memory = s.memory := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem mainWordsAfter_before (s : State) (words : Nat → List (BitVec 32)) (count word : Nat)
    (before : count ≤ word) (within : word < 8) :
    (mainWordsAfter s words count).locals (neonWordName true word) = s.locals (neonWordName true word) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [mainWordsAfter, update, if_neg (word_name_ne word n within (by omega) (by omega))]
    exact ih (by omega)

theorem mainWordsAfter_half (kind : Interpretation) (s : State) (words : Nat → List (BitVec 32)) (count chunk : Nat)
    (within : count ≤ 8) (hc : chunk < 4) :
    (mainWordsAfter s words count).locals (neonHalfName kind true chunk) = s.locals (neonHalfName kind true chunk) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [mainWordsAfter, update, if_neg (word_half_ne kind n chunk (by omega) hc)]
    exact ih (by omega)

theorem mainWordsAfter_word (s : State) (words : Nat → List (BitVec 32)) (count word : Nat)
    (within : count ≤ 8) (done : word < count) :
    (mainWordsAfter s words count).locals (neonWordName true word) = some (.words32 (words word)) := by
  induction count with
  | zero => omega
  | succ n ih =>
    by_cases same : word = n
    · subst word; simp [mainWordsAfter, update]
    · simp only [mainWordsAfter, update, if_neg (word_name_ne word n (by omega) (by omega) same)]
      exact ih (by omega) (by omega)

theorem main_widen_word_exec (kind : Interpretation) (cfg : Config) (s : State) (word : Nat)
    (initial : Nat → List (BitVec 32)) (half : Nat → List (BitVec 16))
    (il : (initial word).length = 4) (hl : (half (word/2)).length = 8)
    (iv : s.locals (neonWordName true word) = some (.words32 (initial word)))
    (hv : s.locals (neonHalfName kind true (word/2)) = some (.halfwords (half (word/2)))) :
    Exec cfg (mainWidenWordCode kind word) s
      (update s (neonWordName true word) (.words32 (mainWidenWord kind initial half word))) := by
  apply Exec.assign
  by_cases parity : word % 2 = 0 <;> cases kind <;>
    simp [mainWidenWordCode, mainWidenWord, rowHalfPrim, eval, intrinsic, saturatingIntrinsic,
      selectionIntrinsic, integerArithmeticIntrinsic, parity, il, hl, iv, hv]

theorem main_widen_exec (kind : Interpretation) (cfg : Config) (s : State) (count : Nat)
    (within : count ≤ neonWidth kind true/4)
    (initial : Nat → List (BitVec 32)) (half : Nat → List (BitVec 16))
    (il : ∀ word, word < neonWidth kind true/4 → (initial word).length = 4)
    (hl : ∀ chunk, chunk < neonChunks kind true → (half chunk).length = 8)
    (iv : ∀ word, word < neonWidth kind true/4 → s.locals (neonWordName true word) = some (.words32 (initial word)))
    (hv : ∀ chunk, chunk < neonChunks kind true → s.locals (neonHalfName kind true chunk) = some (.halfwords (half chunk))) :
    Exec cfg (mainWidenCode kind count) s (mainWordsAfter s (mainWidenWord kind initial half) count) := by
  induction count with
  | zero => exact .skip
  | succ n ih =>
    have nlt : n < neonWidth kind true/4 := by omega
    have n8 : n < 8 := by cases kind <;> simp [neonWidth] at nlt <;> omega
    have chunk : n/2 < neonChunks kind true := by cases kind <;> simp [neonWidth,neonChunks] at nlt ⊢ <;> omega
    have c4 : n/2 < 4 := by omega
    apply appendStatements_exec (ih (by omega))
    apply Exec.seq (main_widen_word_exec kind cfg _ n initial half (il n nlt) (hl (n/2) chunk) ?_ ?_) .skip
    · rw [mainWordsAfter_before s _ n n (by omega) n8]
      exact iv n nlt
    · rw [mainWordsAfter_half kind s _ n (n/2) (by omega) c4]
      exact hv (n/2) chunk

def neonMainWiden (kind : Interpretation) : Stmt :=
  takeStatements (neonWidth kind true/4) (dropStatements (neonChunks kind true+1) (neonBatch kind true))

theorem neon_main_widen_shape (kind : Interpretation) :
    neonMainWiden kind = mainWidenCode kind (neonWidth kind true/4) := by cases kind <;> rfl

end Salty.Kernels.Rdsum
