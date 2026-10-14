import Salty.Proofs.Rdsum.NeonMainRow

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

@[simp] theorem mainRowAfter_memory (kind : Interpretation) (s : State) (ptr : Address)
    (acc : Nat → List (BitVec 16)) : (mainRowAfter kind s ptr acc).memory = s.memory := by cases kind <;> rfl

theorem mainRowAfter_acc (kind : Interpretation) (s : State) (ptr : Address)
    (acc : Nat → List (BitVec 16)) (chunk : Nat) (within : chunk < neonChunks kind true) :
    (mainRowAfter kind s ptr acc).locals (neonHalfName kind true chunk) =
      some (.halfwords (mainRowAcc kind s.memory ptr acc chunk)) := by
  cases kind with
  | signed =>
    have cases : chunk = 0 ∨ chunk = 1 := by simp [neonChunks, neonWidth] at within; omega
    rcases cases with rfl | rfl <;> simp [mainRowAfter, neonHalfName, update]
  | unsigned =>
    have cases : chunk = 0 ∨ chunk = 1 ∨ chunk = 2 ∨ chunk = 3 := by simp [neonChunks, neonWidth] at within; omega
    rcases cases with rfl | rfl | rfl | rfl <;> simp [mainRowAfter, neonHalfName, update]

theorem mainRowAfter_row (kind : Interpretation) (s : State) (ptr : Address)
    (acc : Nat → List (BitVec 16)) (row : Nat) (within : row < 7) :
    (mainRowAfter kind s ptr acc).locals (rowName row) = s.locals (rowName row) := by
  have cases : row = 0 ∨ row = 1 ∨ row = 2 ∨ row = 3 ∨ row = 4 ∨ row = 5 ∨ row = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases kind <;>
    simp [mainRowAfter, mainRowLoaded, mainVin, neonHalfName, rowName, update]

def mainRowsCode (kind : Interpretation) : Nat → Stmt
  | 0 => .skip
  | n+1 => appendStatements (mainRowsCode kind n) (mainRowCode kind (rowName n))

def mainRowsAcc (kind : Interpretation) (m : Memory) (pointers : Nat → Address)
    (initial : Nat → List (BitVec 16)) (count chunk : Nat) : List (BitVec 16) :=
  rowAcc kind (fun row => readBytes m (pointers row+BitVec.ofNat 64 (8*chunk)) 8) (initial chunk) count

def mainRowsAfter (kind : Interpretation) (s : State) (pointers : Nat → Address)
    (initial : Nat → List (BitVec 16)) : Nat → State
  | 0 => s
  | n+1 => mainRowAfter kind (mainRowsAfter kind s pointers initial n) (pointers n)
      (mainRowsAcc kind s.memory pointers initial n)

@[simp] theorem mainRowsAfter_memory (kind : Interpretation) (s : State) (pointers : Nat → Address)
    (initial : Nat → List (BitVec 16)) (count : Nat) :
    (mainRowsAfter kind s pointers initial count).memory = s.memory := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [mainRowsAfter, mainRowAfter_memory, ih]

theorem mainRowsAfter_acc (kind : Interpretation) (s : State) (pointers : Nat → Address)
    (initial : Nat → List (BitVec 16)) (count chunk : Nat) (within : chunk < neonChunks kind true)
    (start : s.locals (neonHalfName kind true chunk) = some (.halfwords (initial chunk))) :
    (mainRowsAfter kind s pointers initial count).locals (neonHalfName kind true chunk) =
      some (.halfwords (mainRowsAcc kind s.memory pointers initial count chunk)) := by
  cases count with
  | zero => exact start
  | succ n =>
    simp only [mainRowsAfter, mainRowAfter_acc kind _ _ _ chunk within, mainRowsAfter_memory]
    rfl

theorem mainRowsAfter_row (kind : Interpretation) (s : State) (pointers : Nat → Address)
    (initial : Nat → List (BitVec 16)) (count row : Nat) (within : row < 7) :
    (mainRowsAfter kind s pointers initial count).locals (rowName row) = s.locals (rowName row) := by
  induction count with
  | zero => rfl
  | succ n ih => rw [mainRowsAfter, mainRowAfter_row kind _ _ _ row within, ih]

/-- Seven source row blocks in their actual order; each chunk retains its own
bounded halfword accumulator. -/
theorem main_rows_exec (kind : Interpretation) (cfg : Config) (s : State) (pointers : Nat → Address)
    (initial : Nat → List (BitVec 16)) (count : Nat) (within : count ≤ 7)
    (hp : ∀ row, row < 7 → s.locals (rowName row) = some (.pointer (pointers row)))
    (ha : ∀ j, j < neonChunks kind true → (initial j).length = 8)
    (hv : ∀ j, j < neonChunks kind true → s.locals (neonHalfName kind true j) = some (.halfwords (initial j)))
    (safe : ∀ row, row < 7 → ∀ j, j < neonChunks kind true → ∀ a,
      Footprint (pointers row+BitVec.ofNat 64 (8*j)) (mainLoadWidth kind) a → s.memory.readable a = true) :
    Exec cfg (mainRowsCode kind count) s (mainRowsAfter kind s pointers initial count) := by
  induction count with
  | zero => exact .skip
  | succ n ih =>
    apply appendStatements_exec (ih (by omega))
    apply main_row_exec kind cfg _ (rowName n) (pointers n) (mainRowsAcc kind s.memory pointers initial n)
    · have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [mainRowsAfter_row kind s pointers initial n n (by omega)]
      exact hp n (by omega)
    · intro j hj
      exact rowAcc_length kind _ (initial j) 8 (ha j hj) (fun _ => readBytes_length ..) n
    · intro j hj
      exact mainRowsAfter_acc kind s pointers initial n j hj (hv j hj)
    · intro j hj a h
      simpa only [mainRowsAfter_memory] using safe n (by omega) j hj a h

/-- Definitional check against the extracted main group, after its six zero
substitutions and two/four declaration skips. -/
theorem main_rows_source_shape (kind : Interpretation) :
    dropStatements (6+neonChunks kind true) (neonGroup kind true) =
      appendStatements (mainRowsCode kind 7) (neonPointersCode true) := by
  cases kind <;> rfl

end Salty.Kernels.Rdsum
