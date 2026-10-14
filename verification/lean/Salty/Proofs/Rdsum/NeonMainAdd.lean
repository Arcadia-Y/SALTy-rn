import Salty.Proofs.Rdsum.NeonMainLoad

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def mainAddCode : Nat → Stmt
  | 0 => .skip
  | n+1 => appendStatements (mainAddCode n)
      (.seq (.assign (neonWordName true n) (.call .addWords32x4
        [.var (mainOldName n), .var (neonWordName true n)])) .skip)

def mainOutputWords (m : Memory) (output : Address) (acc : Nat → List (BitVec 32)) (word : Nat) :=
  storedWords m (output+BitVec.ofNat 64 (16*word)) 4 (acc word)

theorem mainWordsAfter_old (s : State) (acc : Nat → List (BitVec 32)) (count word : Nat)
    (bound : count ≤ 8) (within : word < 8) :
    (mainWordsAfter s acc count).locals (mainOldName word) = s.locals (mainOldName word) := by
  have names : ∀ i : Fin 8, mainOldName word ≠ neonWordName true i.val := by
    have all : ∀ i j : Fin 8, mainOldName i.val ≠ neonWordName true j.val := by decide
    exact all ⟨word,within⟩
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [mainWordsAfter, update, if_neg (names ⟨n,by omega⟩)]
    exact ih (by omega)

theorem main_add_exec (cfg : Config) (s : State) (m : Memory) (output : Address)
    (acc : Nat → List (BitVec 32)) (count : Nat) (bound : count ≤ 8)
    (lengths : ∀ word, word < count → (acc word).length = 4)
    (words : ∀ word, word < count → s.locals (neonWordName true word) = some (.words32 (acc word)))
    (old : ∀ word, word < count → s.locals (mainOldName word) =
      some (.words32 (readWords32 m (output+BitVec.ofNat 64 (16*word)) 4))) :
    Exec cfg (mainAddCode count) s (mainWordsAfter s (mainOutputWords m output acc) count) := by
  induction count with
  | zero => exact .skip
  | succ n ih =>
    apply appendStatements_exec (ih (by omega) (fun word hw => lengths word (by omega))
      (fun word hw => words word (by omega)) (fun word hw => old word (by omega)))
    apply Exec.seq (Exec.assign ?_) .skip
    have av := (mainWordsAfter_before s (mainOutputWords m output acc) n n (by omega) (by omega)).trans (words n (by omega))
    have ov := (mainWordsAfter_old s (mainOutputWords m output acc) n n (by omega) (by omega)).trans (old n (by omega))
    simp [eval, intrinsic, av, ov, lengths n (by omega), mainOutputWords, storedWords]

def neonMainLoadAdd (kind : Interpretation) : Stmt :=
  takeStatements (1+3*(neonWidth kind true/4))
    (dropStatements (9+neonWidth kind true/4) (neonChannels kind true))

def mainLoadAdded (kind : Interpretation) (s : State) (output : Address) (acc : Nat → List (BitVec 32)) : State :=
  mainWordsAfter (mainLoaded (update s "o" (.pointer output)) output (neonWidth kind true/4))
    (mainOutputWords s.memory output acc) (neonWidth kind true/4)

theorem neon_main_load_add_shape (kind : Interpretation) : neonMainLoadAdd kind =
    .seq (.assign "o" (.var "output"))
      (appendStatements (mainLoadCode (neonWidth kind true/4)) (mainAddCode (neonWidth kind true/4))) := by
  cases kind <;> rfl

theorem neon_main_load_add_exec (kind : Interpretation) (cfg : Config) (s : State) (output : Address)
    (acc : Nat → List (BitVec 32))
    (out : s.locals "output" = some (.pointer output))
    (lengths : ∀ word, word < neonWidth kind true/4 → (acc word).length = 4)
    (words : ∀ word, word < neonWidth kind true/4 → s.locals (neonWordName true word) = some (.words32 (acc word)))
    (readable : ∀ a, Footprint output (4*neonWidth kind true) a → s.memory.readable a = true) :
    Exec cfg (neonMainLoadAdd kind) s (mainLoadAdded kind s output acc) := by
  rw [neon_main_load_add_shape]
  apply Exec.seq (t := update s "o" (.pointer output)) (Exec.assign (by simp [eval,out]))
  apply appendStatements_exec (main_load_exec cfg _ output (neonWidth kind true/4) (by simp [update]) ?_)
  · apply main_add_exec cfg _ s.memory output acc _ (by cases kind <;> decide) lengths
    · intro word hw
      rw [mainLoaded_acc _ _ _ _ (by cases kind <;> decide) (by cases kind <;> simp [neonWidth] at hw <;> omega)]
      have no : neonWordName true word ≠ "o" := by
        have all : ∀ i : Fin 8, neonWordName true i.val ≠ "o" := by decide
        exact all ⟨word,by cases kind <;> simp [neonWidth] at hw <;> omega⟩
      simpa only [update, if_neg no] using words word hw
    · intro word hw
      exact mainLoaded_old _ _ _ _ (by cases kind <;> decide) hw
  · simpa only [update] using (show ∀ a, Footprint output (16*(neonWidth kind true/4)) a → s.memory.readable a = true from
      by cases kind <;> simpa [neonWidth] using readable)

@[simp] theorem mainLoadAdded_memory (kind : Interpretation) (s : State) (output : Address) (acc : Nat → List (BitVec 32)) :
    (mainLoadAdded kind s output acc).memory = s.memory := by simp [mainLoadAdded, update]

theorem mainLoadAdded_words (kind : Interpretation) (s : State) (output : Address) (acc : Nat → List (BitVec 32))
    (word : Nat) (within : word < neonWidth kind true/4) :
    (mainLoadAdded kind s output acc).locals (neonWordName true word) =
      some (.words32 (mainOutputWords s.memory output acc word)) :=
  mainWordsAfter_word _ _ _ _ (by cases kind <;> decide) within

end Salty.Kernels.Rdsum
