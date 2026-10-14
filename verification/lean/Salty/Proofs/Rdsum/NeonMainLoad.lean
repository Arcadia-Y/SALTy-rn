import Salty.Proofs.Rdsum.NeonMainInit

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def mainOldName (word : Nat) : String := match word with
  | 0 => "vo0" | 1 => "vo4" | 2 => "vo8" | 3 => "vo12"
  | 4 => "vo16" | 5 => "vo20" | 6 => "vo24" | _ => "vo28"

def mainLoadCode : Nat → Stmt
  | 0 => .skip
  | n+1 => appendStatements (mainLoadCode n)
      (.seq (.assign (mainOldName n) (.call .loadWords32x4 [.var "o"]))
        (.seq (.assign "o" (.offset 4 (.var "o") (.lit 4))) .skip))

def mainLoaded (s : State) (output : Address) : Nat → State
  | 0 => s
  | n+1 => update (update (mainLoaded s output n) (mainOldName n)
      (.words32 (readWords32 s.memory (output+BitVec.ofNat 64 (16*n)) 4)))
      "o" (.pointer (output+BitVec.ofNat 64 (16*(n+1))))

@[simp] theorem mainLoaded_memory (s : State) (output : Address) (count : Nat) :
    (mainLoaded s output count).memory = s.memory := by
  induction count with | zero => rfl | succ n ih => exact ih

theorem mainLoaded_o (s : State) (output : Address) (count : Nat)
    (ho : s.locals "o" = some (.pointer output)) :
    (mainLoaded s output count).locals "o" = some (.pointer (output+BitVec.ofNat 64 (16*count))) := by
  cases count <;> simp [mainLoaded, update, ho]

theorem main_old_ne (i j : Nat) (hi : i < 8) (hj : j < 8) (ne : i ≠ j) : mainOldName i ≠ mainOldName j := by
  have inj : ∀ i j : Fin 8, mainOldName i.val = mainOldName j.val → i = j := by decide
  intro h
  exact ne (congrArg Fin.val (inj ⟨i,hi⟩ ⟨j,hj⟩ h))

theorem mainLoaded_old (s : State) (output : Address) (count word : Nat)
    (bound : count ≤ 8) (done : word < count) :
    (mainLoaded s output count).locals (mainOldName word) =
      some (.words32 (readWords32 s.memory (output+BitVec.ofNat 64 (16*word)) 4)) := by
  have no : mainOldName word ≠ "o" := by
    have all : ∀ i : Fin 8, mainOldName i.val ≠ "o" := by decide
    exact all ⟨word,by omega⟩
  induction count with
  | zero => omega
  | succ n ih =>
    by_cases same : word = n
    · subst word; simp [mainLoaded, update, no]
    · simp only [mainLoaded, update, if_neg no, if_neg (main_old_ne word n (by omega) (by omega) same)]
      exact ih (by omega) (by omega)

theorem mainLoaded_acc (s : State) (output : Address) (count word : Nat)
    (bound : count ≤ 8) (within : word < 8) :
    (mainLoaded s output count).locals (neonWordName true word) = s.locals (neonWordName true word) := by
  have no : neonWordName true word ≠ "o" := by
    have all : ∀ i : Fin 8, neonWordName true i.val ≠ "o" := by decide
    exact all ⟨word,within⟩
  have names : ∀ i : Fin 8, neonWordName true word ≠ mainOldName i.val := by
    have all : ∀ i j : Fin 8, neonWordName true i.val ≠ mainOldName j.val := by decide
    exact all ⟨word,within⟩
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [mainLoaded, update, if_neg no, if_neg (names ⟨n,by omega⟩)]
    exact ih (by omega)

theorem main_load_exec (cfg : Config) (s : State) (output : Address) (count : Nat)
    (ho : s.locals "o" = some (.pointer output))
    (readable : ∀ a, Footprint output (16*count) a → s.memory.readable a = true) :
    Exec cfg (mainLoadCode count) s (mainLoaded s output count) := by
  induction count with
  | zero => exact .skip
  | succ n ih =>
    apply appendStatements_exec (ih (fun a ha => readable a (footprint_mono (by omega) ha)))
    have load := loadBytes_success (mainLoaded s output n).memory (output+BitVec.ofNat 64 (16*n)) 16
      (fun a ha => by rw [mainLoaded_memory]; exact readable a (footprint_shift_within (by omega) ha))
    simp only [mainLoaded_memory] at load
    have no : "o" ≠ mainOldName n := by unfold mainOldName; split <;> decide
    have o := mainLoaded_o s output n ho
    apply run_sound (fuel := 4)
    simp [run, eval, intrinsic, update, o, no, load, mainLoaded_memory, decodeWords32_read s.memory (output+BitVec.ofNat 64 (16*n)) 4,
      mainLoaded, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

end Salty.Kernels.Rdsum
