import Salty.Proofs.Rdsum.NeonMainBatchSum

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

structure NeonMainBatchLocals (kind : Interpretation) (s : State) (pointers : Nat → Address) (zero : Address)
    (remaining stride : Nat) (initial : Nat → BitVec 32) : Prop where
  rows : ∀ i, i < 7 → s.locals (rowName i) = some (.pointer (pointers i))
  zero : s.locals "zero" = some (.pointer zero)
  remaining : s.locals "r" = some (.integer remaining)
  increment : s.locals "input_increment" = some (.integer (7*stride))
  words : ∀ word, word < neonWidth kind true/4 →
    s.locals (neonWordName true word) = some (.words32 (wordValues initial word))

def mainReset (kind : Interpretation) : Stmt := takeStatements (neonChunks kind true) (neonBatch kind true)

def mainResetCode (kind : Interpretation) : Stmt :=
  let zero := Expr.call .dupI16x8 [.cast (match kind with | .signed => .i16 | .unsigned => .u16) (.lit 0)]
  .seq (.assign (neonHalfName kind true 0) zero)
  (.seq (.assign (neonHalfName kind true 1) zero)
    (match kind with
    | .signed => .skip
    | .unsigned => .seq (.assign "vacc16_20" zero) (.seq (.assign "vacc16_28" zero) .skip)))

def mainResetAfter (kind : Interpretation) (s : State) : State :=
  let s := update s (neonHalfName kind true 0) (.halfwords (List.replicate 8 0))
  let s := update s (neonHalfName kind true 1) (.halfwords (List.replicate 8 0))
  match kind with
  | .signed => s
  | .unsigned => update (update s "vacc16_20" (.halfwords (List.replicate 8 0))) "vacc16_28" (.halfwords (List.replicate 8 0))

def mainStarted (kind : Interpretation) (s : State) (remaining : Nat) : State :=
  update (mainResetAfter kind s) "current_batch" (.integer (batchSize remaining))

theorem main_reset_shape (kind : Interpretation) : mainReset kind = mainResetCode kind := by cases kind <;> rfl

theorem main_reset_exec (kind : Interpretation) (cfg : Config) (s : State) :
    Exec cfg (mainReset kind) s (mainResetAfter kind s) := by
  rw [main_reset_shape]
  cases kind <;> apply run_sound (fuel := 7) <;>
    simp [mainResetCode, mainResetAfter, run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic,
      show convert .i16 0 = 0 from rfl, show convert .u16 0 = 0 from rfl]

theorem main_start_exec (kind : Interpretation) (cfg : Config) (s : State) (remaining : Nat)
    (bound : remaining < 2^31) (hr : s.locals "r" = some (.integer remaining)) :
    Exec cfg (.seq (mainReset kind) (neonCount kind true)) s (mainStarted kind s remaining) := by
  apply Exec.seq (main_reset_exec kind cfg s)
  apply neon_count_exec kind true cfg _ remaining bound
  cases kind <;> simpa [mainResetAfter, update, neonHalfName, neonRemaining] using hr

@[simp] theorem mainStarted_memory (kind : Interpretation) (s : State) (remaining : Nat) :
    (mainStarted kind s remaining).memory = s.memory := by cases kind <;> rfl

theorem mainStarted_group (kind : Interpretation) (s : State) (pointers : Nat → Address) (zero : Address)
    (remaining stride : Nat) (initial : Nat → BitVec 32)
    (loc : NeonMainBatchLocals kind s pointers zero remaining stride initial) :
    NeonMainLocals kind (mainStarted kind s remaining) pointers zero (batchSize remaining) (7*stride) zeroMainAcc := by
  constructor
  · intro i hi
    have hp := loc.rows i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases kind <;>
      simpa [mainStarted, mainResetAfter, update, rowName, neonHalfName] using hp
  · cases kind <;> simpa [mainStarted, mainResetAfter, update, neonHalfName] using loc.zero
  · simp [mainStarted, update]
  · cases kind <;> simpa [mainStarted, mainResetAfter, update, neonHalfName] using loc.increment
  · intro j hj
    cases kind with
    | signed =>
      have cases : j = 0 ∨ j = 1 := by simp [neonChunks,neonWidth] at hj; omega
      rcases cases with rfl | rfl <;> simp [mainStarted, mainResetAfter, update, neonHalfName, zeroMainAcc, List.map_const']
    | unsigned =>
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [neonChunks,neonWidth] at hj; omega
      rcases cases with rfl | rfl | rfl | rfl <;> simp [mainStarted, mainResetAfter, update, neonHalfName, zeroMainAcc, List.map_const']

theorem main_start_word_frame (kind : Interpretation) (word : Nat) (within : word < 8) :
    (Stmt.seq (mainReset kind) (neonCount kind true)).writes (neonWordName true word) = false := by
  have all : ∀ word : Fin 8, (Stmt.seq (mainReset kind) (neonCount kind true)).writes (neonWordName true word.val) = false := by
    cases kind <;> decide
  exact all ⟨word,within⟩

theorem main_finish_word_frame (kind : Interpretation) (word : Nat) (within : word < 8) :
    (neonFinish kind true).writes (neonWordName true word) = false := by
  have all : ∀ word : Fin 8, (neonFinish kind true).writes (neonWordName true word.val) = false := by
    cases kind <;> decide
  exact all ⟨word,within⟩

end Salty.Kernels.Rdsum
