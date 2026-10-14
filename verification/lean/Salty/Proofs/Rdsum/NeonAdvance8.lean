import Salty.Proofs.Rdsum.NeonStore8

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def neonAdvance8 (kind : Interpretation) : Stmt := dropStatements 8 (branchYes (neonTailOutput kind))

def neonAdvance8Code : Stmt :=
  .seq (.assign "channels" (.cast .u64 (.bin .sub (.var "channels") (.cast .u64 (.lit 8)))))
  (.seq (.assign "input" (.intToPtr (.cast .u64 (.bin .add (.ptrToInt (.var "input"))
    (.cast .u64 (.bin .mul (.cast .u64 (.lit 8)) (.lit 1))))))) .skip)

theorem neon_advance8_shape (kind : Interpretation) : neonAdvance8 kind = neonAdvance8Code := by
  cases kind <;> rfl

def neonAdvanced8 (s : State) (input : Address) (channels : Nat) : State :=
  update (update s "channels" (.integer (channels-8 : Nat))) "input" (.pointer (input+8))

theorem neon_advance8_exec (kind : Interpretation) (cfg : Config) (s : State) (input : Address)
    (channels : Nat) (bound : channels < 2^64) (within : 8 ≤ channels)
    (hi : s.locals "input" = some (.pointer input))
    (hc : s.locals "channels" = some (.integer channels)) :
    Exec cfg (neonAdvance8 kind) s (neonAdvanced8 s input channels) := by
  have sub : convert .u64 ((channels : Int)-8) = (channels-8 : Nat) := by
    simpa using cast_sub channels 8 within bound
  have ptr : BitVec.ofInt 64 (convert .u64 ((input.toNat : Int)+8)) = input+8 := by
    simp only [convert, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.ofInt_add]
    simp
  rw [neon_advance8_shape]
  apply run_sound (fuel := 5)
  simp [neonAdvance8Code, neonAdvanced8, run, eval, binary, update, hi, hc, sub, ptr,
    show convert .u64 8 = 8 from rfl]

/-- Full true branch, including source-level channel and input updates. -/
theorem neon_output8_exec (kind : Interpretation) (cfg : Config) (s : State) (input output : Address)
    (channels : Nat) (bound : channels < 2^64) (within : 8 ≤ channels)
    (low high : List (BitVec 32)) (ll : low.length = 4) (hl : high.length = 4)
    (hi : s.locals "input" = some (.pointer input))
    (hc : s.locals "channels" = some (.integer channels))
    (out : s.locals "output" = some (.pointer output))
    (lo : s.locals "vacc0_2" = some (.words32 low))
    (hv : s.locals "vacc1" = some (.words32 high))
    (readable : ∀ a, Footprint output 32 a → s.memory.readable a = true)
    (writable : ∀ a, Footprint output 32 a → s.memory.writable a = true) :
    Exec cfg (branchYes (neonTailOutput kind)) s
      (neonAdvanced8 (neonStored8 s output low high) input channels) := by
  apply exec_take_drop (t := neonStored8 s output low high) 8
  · exact neon_store8_exec kind cfg s output low high ll hl out lo hv readable writable
  · exact neon_advance8_exec kind cfg _ input channels bound within
      (by simp [neonStored8, update, hi]) (by simp [neonStored8, update, hc])

end Salty.Kernels.Rdsum
