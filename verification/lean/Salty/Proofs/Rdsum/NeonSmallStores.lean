import Salty.Proofs.Rdsum.NeonStore8

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def branchNo : Stmt → Stmt
  | .branch _ _ no => no
  | _ => .skip

def neonSmallStore (kind : Interpretation) (two : Bool) : Stmt :=
  branchYes (firstStatement (dropStatements (if two then 1 else 0) (branchNo (neonTailOutput kind))))

def neonStore4Code : Stmt :=
  .seq (.assign "vo" (.call .loadWords32x4 [.var "output"]))
  (.seq (.assign "vo" (.call .addWords32x4 [.var "vo", .var "vacc0_2"]))
  (.seq (.effect .storeWords32x4 [.var "output", .var "vo"])
  (.seq (.assign "output" (.offset 4 (.var "output") (.lit 4)))
  (.seq (.assign "vacc0_2" (.var "vacc1")) .skip))))

def neonStore2Code : Stmt :=
  .seq (.assign "vo_2" (.call .loadWords32x2 [.var "output"]))
  (.seq (.assign "vo_2" (.call .addWords32x2 [.var "vo_2", .call .lowWords32x2 [.var "vacc0_2"]]))
  (.seq (.effect .storeWords32x2 [.var "output", .var "vo_2"])
  (.seq (.assign "output" (.offset 4 (.var "output") (.lit 2)))
  (.seq (.assign "vacc0_2" (.call .extractWords32x4 [.var "vacc0_2", .var "vacc0_2", .lit 2])) .skip))))

theorem neon_store4_shape (kind : Interpretation) : neonSmallStore kind false = neonStore4Code := by
  cases kind <;> rfl

theorem neon_store2_shape (kind : Interpretation) : neonSmallStore kind true = neonStore2Code := by
  cases kind <;> rfl

def neonSmallStored (s : State) (output : Address) (width : Nat) (name : String)
    (acc next : List (BitVec 32)) : State :=
  let words := storedWords s.memory output width acc
  let s := update s name (.words32 words)
  let s := {s with memory := writeBytes s.memory output (encodeWords32 words)}
  let s := update s "output" (.pointer (output+BitVec.ofNat 64 (4*width)))
  update s "vacc0_2" (.words32 next)

def rotateWords2 (acc : List (BitVec 32)) : List (BitVec 32) := ((acc++acc).drop 2).take 4

theorem neon_store4_exec (kind : Interpretation) (cfg : Config) (s : State) (output : Address)
    (low high : List (BitVec 32)) (ll : low.length = 4)
    (out : s.locals "output" = some (.pointer output))
    (lo : s.locals "vacc0_2" = some (.words32 low))
    (hi : s.locals "vacc1" = some (.words32 high))
    (readable : ∀ a, Footprint output 16 a → s.memory.readable a = true)
    (writable : ∀ a, Footprint output 16 a → s.memory.writable a = true) :
    Exec cfg (neonSmallStore kind false) s (neonSmallStored s output 4 "vo" low high) := by
  have load := loadBytes_success s.memory output 16 readable
  have store := storeBytes_success s.memory output (encodeWords32 (storedWords s.memory output 4 low))
    (by simpa only [encodeWords32_length, storedWords_length _ _ _ _ ll] using writable)
  simp only [storedWords] at store
  rw [neon_store4_shape]
  apply run_sound (fuel := 8)
  simp [neonStore4Code, neonSmallStored, run, eval, intrinsic, effect, update,
    out, lo, hi, ll, load, decodeWords32_read s.memory output 4, storedWords, store]
  funext x
  by_cases h : x = "vo" <;> simp [h]

theorem neon_store2_exec (kind : Interpretation) (cfg : Config) (s : State) (output : Address)
    (acc : List (BitVec 32)) (len : acc.length = 4)
    (out : s.locals "output" = some (.pointer output))
    (av : s.locals "vacc0_2" = some (.words32 acc))
    (readable : ∀ a, Footprint output 8 a → s.memory.readable a = true)
    (writable : ∀ a, Footprint output 8 a → s.memory.writable a = true) :
    Exec cfg (neonSmallStore kind true) s (neonSmallStored s output 2 "vo_2" (acc.take 2) (rotateWords2 acc)) := by
  have load := loadBytes_success s.memory output 8 readable
  have al : (acc.take 2).length = 2 := by simp [len]
  have store := storeBytes_success s.memory output (encodeWords32 (storedWords s.memory output 2 (acc.take 2)))
    (by simpa only [encodeWords32_length, storedWords_length _ _ _ _ al] using writable)
  simp only [storedWords] at store
  rw [neon_store2_shape]
  apply run_sound (fuel := 8)
  simp [neonStore2Code, neonSmallStored, rotateWords2, run, eval, intrinsic, effect, update,
    out, av, len, load, decodeWords32_read s.memory output 2, storedWords, store]
  funext x
  by_cases h : x = "vo_2" <;> simp [h]

end Salty.Kernels.Rdsum
