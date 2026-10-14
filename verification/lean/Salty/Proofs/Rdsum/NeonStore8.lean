import Salty.Proofs.Rdsum.NeonTailInit
import Salty.Proofs.Rdsum.WordMemory

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- The eight-channel branch loads both old vectors before either store. -/
def neonTailOutput (kind : Interpretation) : Stmt :=
  firstStatement (dropStatements 12 (neonChannels kind false))
def neonStore8 (kind : Interpretation) : Stmt := takeStatements 8 (branchYes (neonTailOutput kind))

def neonStore8Code : Stmt :=
  .seq (.assign "vo0_2" (.call .loadWords32x4 [.var "output"]))
  (.seq (.assign "vo1" (.call .loadWords32x4 [.offset 4 (.var "output") (.lit 4)]))
  (.seq (.assign "vo0_2" (.call .addWords32x4 [.var "vo0_2", .var "vacc0_2"]))
  (.seq (.assign "vo1" (.call .addWords32x4 [.var "vo1", .var "vacc1"]))
  (.seq (.effect .storeWords32x4 [.var "output", .var "vo0_2"])
  (.seq (.assign "output" (.offset 4 (.var "output") (.lit 4)))
  (.seq (.effect .storeWords32x4 [.var "output", .var "vo1"])
  (.seq (.assign "output" (.offset 4 (.var "output") (.lit 4))) .skip)))))))

theorem neon_store8_shape (kind : Interpretation) : neonStore8 kind = neonStore8Code := by
  cases kind <;> rfl

def neonStored8 (s : State) (output : Address) (low high : List (BitVec 32)) : State :=
  let left := storedWords s.memory output 4 low
  let right := storedWords s.memory (output+16) 4 high
  let s := update s "vo0_2" (.words32 left)
  let s := update s "vo1" (.words32 right)
  let s := {s with memory := writeBytes s.memory output (encodeWords32 left)}
  let s := update s "output" (.pointer (output+16))
  let s := {s with memory := writeBytes s.memory (output+16) (encodeWords32 right)}
  update s "output" (.pointer (output+16+16))

/-- Permission-checked execution of the actual pair of load/add/store vectors. -/
theorem neon_store8_exec (kind : Interpretation) (cfg : Config) (s : State) (output : Address)
    (low high : List (BitVec 32)) (ll : low.length = 4) (hl : high.length = 4)
    (out : s.locals "output" = some (.pointer output))
    (lo : s.locals "vacc0_2" = some (.words32 low))
    (hi : s.locals "vacc1" = some (.words32 high))
    (readable : ∀ a, Footprint output 32 a → s.memory.readable a = true)
    (writable : ∀ a, Footprint output 32 a → s.memory.writable a = true) :
    Exec cfg (neonStore8 kind) s (neonStored8 s output low high) := by
  have r0 := loadBytes_success s.memory output 16 (fun a ha => readable a (footprint_mono (by omega) ha))
  have r1 := loadBytes_success s.memory (output+16) 16 (fun a ha => readable a
    (footprint_shift_within (start := 16) (by omega) ha))
  have w0 := storeBytes_success s.memory output (encodeWords32 (storedWords s.memory output 4 low))
    (fun a ha => writable a (footprint_mono (by simp [ll]) ha))
  have w1 := storeBytes_success
    (writeBytes s.memory output (encodeWords32 (storedWords s.memory output 4 low)))
    (output+16) (encodeWords32 (storedWords s.memory (output+16) 4 high))
    (fun a ha => by
      simp only [writeBytes_writable]
      apply writable a
      apply footprint_shift_within (start := 16) (by simp [hl]) ha)
  simp only [storedWords, BitVec.ofNat_eq_ofNat] at w0 w1 r1
  rw [neon_store8_shape]
  apply run_sound (fuel := 11)
  simp [neonStore8Code, neonStored8, run, eval, intrinsic, effect, update, out, lo, hi,
    r0, r1, decodeWords32_read s.memory output 4,
    decodeWords32_read s.memory (output+16#64) 4, ll, hl, w0, w1, storedWords]

  funext x
  by_cases a : x = "output" <;> by_cases b : x = "vo0_2" <;> by_cases c : x = "vo1" <;> simp [a,b,c]

theorem neonStored8_memory (s : State) (output : Address) (low high : List (BitVec 32))
    (ll : low.length = 4) (hl : high.length = 4) :
    (neonStored8 s output low high).memory =
      writeBytes s.memory output (encodeWords32 (storedWords s.memory output 8 (low++high))) := by
  have join := storedWords_write_join s.memory output low high
  simpa only [ll, hl] using join

@[simp] theorem neonStored8_output (s : State) (output : Address) (low high : List (BitVec 32)) :
    (neonStored8 s output low high).locals "output" = some (.pointer (output+32)) := by
  simp [neonStored8, update, BitVec.add_assoc]

end Salty.Kernels.Rdsum
