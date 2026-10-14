import Salty.Proofs.Rdsum.NeonTailControl

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def neonLastStores (kind : Interpretation) : Stmt := dropStatements 1 (branchNo (neonTailOutput kind))

theorem neon_last_stores_shape (kind : Interpretation) : neonLastStores kind =
    .seq (neonTailBranch kind 1) (.seq (neonTailBranch kind 2) (neonTailClear kind)) := by
  cases kind <;> rfl

def afterTwo (s : State) (output : Address) (acc : List (BitVec 32)) : State :=
  neonSmallStored s output 2 "vo_2" (acc.take 2) (rotateWords2 acc)

def lastStored (s : State) (output : Address) (acc : List (BitVec 32)) (n : Nat) : State :=
  let s := match n with
    | 0 => s
    | 1 => neonScalarStored s output acc[0]!
    | 2 => afterTwo s output acc
    | _ => neonScalarStored (afterTwo s output acc) (output+8) (rotateWords2 acc)[0]!
  update s "channels" (.integer 0)

def LastStoreDefined (kind : Interpretation) (s : State) (output : Address)
    (acc : List (BitVec 32)) (n : Nat) : Prop :=
  match n with
  | 1 => ScalarStoreDefined kind (readWord32 s.memory output) acc[0]!
  | 3 => ScalarStoreDefined kind (readWord32 (afterTwo s output acc).memory (output+8)) (rotateWords2 acc)[0]!
  | _ => True

@[simp] theorem rotateWords2_length (acc : List (BitVec 32)) (len : acc.length = 4) :
    (rotateWords2 acc).length = 4 := by simp [rotateWords2, len]

/-- The 2/1 branches retain the original channel count until the final clear. -/
theorem neon_last_stores_exec (kind : Interpretation) (cfg : Config) (s : State) (output : Address)
    (acc : List (BitVec 32)) (len : acc.length = 4) (channels n : Nat)
    (bound : channels < 2^64) (small : n < 4)
    (bit2 : channels &&& 2 = n &&& 2) (bit1 : channels &&& 1 = n &&& 1)
    (hc : s.locals "channels" = some (.integer channels))
    (out : s.locals "output" = some (.pointer output))
    (av : s.locals "vacc0_2" = some (.words32 acc))
    (readable : ∀ a, Footprint output (4*n) a → s.memory.readable a = true)
    (writable : ∀ a, Footprint output (4*n) a → s.memory.writable a = true)
    (defined : LastStoreDefined kind s output acc n) :
    Exec cfg (neonLastStores kind) s (lastStored s output acc n) := by
  rw [neon_last_stores_shape]
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact .seq (tail_branch_no kind cfg s channels 1 bound (by decide) hc (by simpa [tailBitMask] using bit2))
      (.seq (tail_branch_no kind cfg s channels 2 bound (by decide) hc (by simpa [tailBitMask] using bit1))
        (neon_tail_clear_exec kind cfg s))
  · have scalar := neon_scalar_store_exec kind cfg s output acc len out av readable writable defined
    exact .seq (tail_branch_no kind cfg s channels 1 bound (by decide) hc (by simpa [tailBitMask] using bit2))
      (.seq (tail_branch_yes kind cfg s _ channels 2 bound (by decide) hc
        (by simp [tailBitMask, bit1]) scalar) (neon_tail_clear_exec kind cfg _))
  · have pair := neon_store2_exec kind cfg s output acc len out av readable writable
    have count : (afterTwo s output acc).locals "channels" = some (.integer channels) := by
      simp [afterTwo, neonSmallStored, update, hc]
    exact .seq (tail_branch_yes kind cfg s _ channels 1 bound (by decide) hc
      (by simp [tailBitMask, bit2]) pair)
      (.seq (tail_branch_no kind cfg _ channels 2 bound (by decide) count
        (by simpa [tailBitMask] using bit1)) (neon_tail_clear_exec kind cfg _))
  · have pair := neon_store2_exec kind cfg s output acc len out av
      (fun a ha => readable a (footprint_mono (by decide) ha))
      (fun a ha => writable a (footprint_mono (by decide) ha))
    have count : (afterTwo s output acc).locals "channels" = some (.integer channels) := by
      simp [afterTwo, neonSmallStored, update, hc]
    have scalar := neon_scalar_store_exec kind cfg (afterTwo s output acc) (output+8)
      (rotateWords2 acc) (rotateWords2_length acc len)
      (by simp [afterTwo, neonSmallStored, update])
      (by simp [afterTwo, neonSmallStored, update])
      (fun a ha => by
        simp only [afterTwo, neonSmallStored, update, writeBytes_readable]
        exact readable a (footprint_shift_within (start := 8) (by decide) ha))
      (fun a ha => by
        simp only [afterTwo, neonSmallStored, update, writeBytes_writable]
        exact writable a (footprint_shift_within (start := 8) (by decide) ha)) defined
    exact .seq (tail_branch_yes kind cfg s _ channels 1 bound (by decide) hc
      (by simp [tailBitMask, bit2]) pair)
      (.seq (tail_branch_yes kind cfg _ _ channels 2 bound (by decide) count
        (by simp [tailBitMask, bit1]) scalar) (neon_tail_clear_exec kind cfg _))

end Salty.Kernels.Rdsum
