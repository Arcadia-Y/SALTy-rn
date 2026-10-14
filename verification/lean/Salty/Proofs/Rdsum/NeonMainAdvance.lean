import Salty.Proofs.Rdsum.NeonMainWork

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def neonMainAdvance (kind : Interpretation) : Stmt :=
  dropStatements (10+6*(neonWidth kind true/4)) (neonChannels kind true)

def neonMainSubtract (kind : Interpretation) : Stmt :=
  dropStatements 1 (loopBody (firstStatement (dropStatements 5 (neonProgram kind))))

def neonMainChannelIteration (kind : Interpretation) : Stmt :=
  loopBody (firstStatement (dropStatements 5 (neonProgram kind)))

theorem neon_main_advance_shape (kind : Interpretation) : neonMainAdvance kind =
    .seq (.assign "input" (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var "input"))
      (.cast .u64 (.bin .mul (.cast .u64 (.lit (neonWidth kind true))) (.lit 1))))))) .skip := by
  cases kind <;> rfl

theorem neon_main_subtract_shape (kind : Interpretation) : neonMainSubtract kind =
    .assign "channels" (.cast .u64 (.bin .sub (.var "channels") (.cast .u64 (.lit (neonWidth kind true))))) := by
  cases kind <;> rfl

theorem neon_main_advance_exec (kind : Interpretation) (cfg : Config) (s : State) (input : Address)
    (hi : s.locals "input" = some (.pointer input)) :
    Exec cfg (neonMainAdvance kind) s (update s "input" (.pointer (input+BitVec.ofNat 64 (neonWidth kind true)))) := by
  have ptr : ∀ width : Nat, BitVec.ofInt 64 (convert .u64 ((input.toNat : Int)+width)) = input+BitVec.ofNat 64 width := by
    intro width
    simp only [convert, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofInt_add]
  have p16 : BitVec.ofInt 64 (convert .u64 ((input.toNat : Int)+16)) = input+16 := by simpa using ptr 16
  have p32 : BitVec.ofInt 64 (convert .u64 ((input.toNat : Int)+32)) = input+32 := by simpa using ptr 32
  rw [neon_main_advance_shape]
  apply run_sound (fuel := 3)
  cases kind <;> simp [neonWidth, run, eval, binary, hi, p16, p32,
    show convert .u64 16 = 16 from rfl, show convert .u64 32 = 32 from rfl]

theorem neon_main_subtract_exec (kind : Interpretation) (cfg : Config) (s : State) (channels : Nat)
    (bound : channels < 2^64) (within : neonWidth kind true ≤ channels)
    (hc : s.locals "channels" = some (.integer channels)) :
    Exec cfg (neonMainSubtract kind) s (update s "channels" (.integer (channels-neonWidth kind true : Nat))) := by
  have sub := cast_sub channels (neonWidth kind true) within bound
  rw [neon_main_subtract_shape]
  apply Exec.assign
  cases kind <;> simp only [neonWidth, ↓reduceIte] at sub ⊢
  all_goals simp [eval, binary, hc,
    show convert .u64 16 = 16 from rfl, show convert .u64 32 = 32 from rfl]
  all_goals simpa using sub

end Salty.Kernels.Rdsum
