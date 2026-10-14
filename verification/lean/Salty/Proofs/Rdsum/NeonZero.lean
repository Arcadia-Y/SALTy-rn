import Salty.Proofs.Rdsum.NeonShape

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def neonZeroBranch (main : Bool) (i : Nat) (strict : Bool) (cutoff : Int) : Stmt :=
  .branch (.bin (if strict then .lt else .le) (.var (neonCurrent main)) (.lit cutoff))
    (.seq (.assign (neonRowName main i) (.var "zero")) .skip) .skip

theorem neon_zero_branch_exec (cfg : Config) (s : State) (main : Bool) (i : Nat) (strict : Bool)
    (cutoff r : Int) (z : Address)
    (hr : s.locals (neonCurrent main) = some (.integer r))
    (hz : s.locals "zero" = some (.pointer z)) :
    Exec cfg (neonZeroBranch main i strict cutoff) s (zeroAfter s (neonRowName main i) strict cutoff r z) := by
  apply run_sound (fuel := 5)
  cases strict <;> simp only [neonZeroBranch, zeroAfter, zeroWhen, Bool.false_eq_true, ↓reduceIte]
  · by_cases h : r ≤ cutoff <;> simp [run, eval, binary, truth, hr, hz, h]
  · by_cases h : r < cutoff <;> simp [run, eval, binary, truth, hr, hz, h]

def neonZeroBranches (main : Bool) : Stmt :=
  .seq (neonZeroBranch main 1 true 2) (.seq (neonZeroBranch main 2 false 2)
  (.seq (neonZeroBranch main 3 true 4) (.seq (neonZeroBranch main 4 false 4)
  (.seq (neonZeroBranch main 5 true 6) (.seq (neonZeroBranch main 6 false 6) .skip)))))

theorem neon_zero_shape (kind : Interpretation) (main : Bool) :
    takeStatements 6 (neonGroup kind main) = neonZeroBranches main := by
  cases main <;> cases kind <;> rfl

def neonZerosAfter (main : Bool) (s : State) (r : Int) (z : Address) : State :=
  let s := zeroAfter s (neonRowName main 1) true 2 r z
  let s := zeroAfter s (neonRowName main 2) false 2 r z
  let s := zeroAfter s (neonRowName main 3) true 4 r z
  let s := zeroAfter s (neonRowName main 4) false 4 r z
  let s := zeroAfter s (neonRowName main 5) true 6 r z
  zeroAfter s (neonRowName main 6) false 6 r z

theorem neon_zeros_exec (cfg : Config) (s : State) (main : Bool) (r : Int) (z : Address)
    (hr : s.locals (neonCurrent main) = some (.integer r))
    (hz : s.locals "zero" = some (.pointer z)) :
    Exec cfg (neonZeroBranches main) s (neonZerosAfter main s r z) := by
  unfold neonZeroBranches neonZerosAfter
  repeat' apply Exec.seq (neon_zero_branch_exec cfg _ main _ _ _ r z ?_ ?_)
  all_goals
    first
    | exact .skip
    | cases main <;> simp [zeroAfter_frame, neonRowName, neonCurrent, rowName] at hr ⊢ <;> assumption
    | cases main <;> simp [zeroAfter_frame, neonRowName, neonCurrent, rowName, hz]

@[simp] theorem neonZerosAfter_memory (main : Bool) (s : State) (r : Int) (z : Address) :
    (neonZerosAfter main s r z).memory = s.memory := by simp [neonZerosAfter]

theorem neonZerosAfter_row (main : Bool) (s : State) (r : Int) (z : Address) (i : Nat) (hi : i < 7) :
    (neonZerosAfter main s r z).locals (neonRowName main i) =
      if 0 < i ∧ r ≤ (i : Int) then some (.pointer z) else s.locals (neonRowName main i) := by
  have h1 : r < 2 ↔ r ≤ 1 := by omega
  have h3 : r < 4 ↔ r ≤ 3 := by omega
  have h5 : r < 6 ↔ r ≤ 5 := by omega
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases main <;>
    simp [neonZerosAfter, zeroAfter_locals, zeroWhen, neonRowName, rowName, h1, h3, h5]

end Salty.Kernels.Rdsum
