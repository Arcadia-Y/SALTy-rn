import Salty.Proofs.Rdsum.NeonMainAdd

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def mainStoreCode : Nat → Stmt
  | 0 => .skip
  | n+1 => appendStatements (mainStoreCode n)
      (.seq (.effect .storeWords32x4 [.var "output", .var (neonWordName true n)])
        (.seq (.assign "output" (.offset 4 (.var "output") (.lit 4))) .skip))

def mainStored (s : State) (output : Address) (acc : Nat → List (BitVec 32)) : Nat → State
  | 0 => s
  | n+1 =>
    let t := mainStored s output acc n
    update {t with memory := writeBytes t.memory (output+BitVec.ofNat 64 (16*n)) (encodeWords32 (acc n))}
      "output" (.pointer (output+BitVec.ofNat 64 (16*(n+1))))

def mainWordPrefix (acc : Nat → List (BitVec 32)) : Nat → List (BitVec 32)
  | 0 => []
  | n+1 => mainWordPrefix acc n ++ acc n

theorem mainWordPrefix_length (acc : Nat → List (BitVec 32)) (count : Nat)
    (lengths : ∀ word, word < count → (acc word).length = 4) :
    (mainWordPrefix acc count).length = 4*count := by
  induction count with
  | zero => rfl
  | succ n ih => simp [mainWordPrefix, ih (fun word hw => lengths word (by omega)), lengths n (by omega), Nat.mul_add]

theorem mainStored_memory (s : State) (output : Address) (acc : Nat → List (BitVec 32)) (count : Nat)
    (lengths : ∀ word, word < count → (acc word).length = 4) :
    (mainStored s output acc count).memory = writeBytes s.memory output (encodeWords32 (mainWordPrefix acc count)) := by
  induction count with
  | zero => rfl
  | succ n ih =>
    simp only [mainStored, update, mainWordPrefix, encodeWords32_append, writeBytes_append,
      encodeWords32_length, mainWordPrefix_length acc n (fun word hw => lengths word (by omega)),
      ih (fun word hw => lengths word (by omega))]
    congr 2
    congr 1
    omega

theorem mainStored_output (s : State) (output : Address) (acc : Nat → List (BitVec 32)) (count : Nat)
    (out : s.locals "output" = some (.pointer output)) :
    (mainStored s output acc count).locals "output" = some (.pointer (output+BitVec.ofNat 64 (16*count))) := by
  cases count <;> simp [mainStored, update, out]

theorem mainStored_acc (s : State) (output : Address) (acc : Nat → List (BitVec 32)) (count word : Nat) :
    (mainStored s output acc count).locals (neonWordName true word) = s.locals (neonWordName true word) := by
  have ne : neonWordName true word ≠ "output" := by unfold neonWordName; simp only [↓reduceIte]; split <;> decide
  induction count with
  | zero => rfl
  | succ n ih => simp only [mainStored, update, if_neg ne]; exact ih

theorem main_store_exec (cfg : Config) (s : State) (output : Address) (acc : Nat → List (BitVec 32))
    (count : Nat) (out : s.locals "output" = some (.pointer output))
    (lengths : ∀ word, word < count → (acc word).length = 4)
    (words : ∀ word, word < count → s.locals (neonWordName true word) = some (.words32 (acc word)))
    (writable : ∀ a, Footprint output (16*count) a → s.memory.writable a = true) :
    Exec cfg (mainStoreCode count) s (mainStored s output acc count) := by
  induction count with
  | zero => exact .skip
  | succ n ih =>
    have lens : ∀ word, word < n → (acc word).length = 4 := fun word hw => lengths word (by omega)
    apply appendStatements_exec (ih lens (fun word hw => words word (by omega))
      (fun a ha => writable a (footprint_mono (by omega) ha)))
    have store := storeBytes_success (mainStored s output acc n).memory (output+BitVec.ofNat 64 (16*n)) (encodeWords32 (acc n))
      (fun a ha => by
        rw [mainStored_memory _ _ _ _ lens, writeBytes_writable]
        exact writable a (footprint_shift_within (by simp [lengths n (by omega)]; omega) ha))
    have ov := mainStored_output s output acc n out
    have av := (mainStored_acc s output acc n n).trans (words n (by omega))
    apply run_sound (fuel := 4)
    simp [run, eval, effect, update, ov, av, lengths n (by omega), store, mainStored,
      Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

end Salty.Kernels.Rdsum
