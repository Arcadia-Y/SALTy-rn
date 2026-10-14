import Salty.Proofs.Rdsum.RvvChannelInit

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def rvvStore (kind : Interpretation) : Stmt := takeStatements 3 (dropStatements 11 (rvvChannels kind))

def storedWords (m : Memory) (output : Address) (width : Nat) (acc : List (BitVec 32)) : List (BitVec 32) :=
  List.zipWith (· + ·) (readWords32 m output width) acc

def storeAfter (s : State) (output : Address) (width : Nat) (acc : List (BitVec 32)) : State :=
  let words := storedWords s.memory output width acc
  let s := update s "vo" (.words32 words)
  {s with memory := writeBytes s.memory output (encodeWords32 words)}

@[simp] theorem storedWords_length (m : Memory) (output : Address) (width : Nat) (acc : List (BitVec 32))
    (len : acc.length = width) : (storedWords m output width acc).length = width := by
  simp [storedWords, len]

theorem rvv_store_shape (kind : Interpretation) : rvvStore kind =
    .seq (.assign "vo" (.call .loadWords32RVV [.var "output", .var "vl"]))
    (.seq (.assign "vo" (.call .addWords32RVV [.var "vo", .var (accumulatorName kind), .var "vl"]))
    (.seq (.effect .storeWords32RVV [.var "output", .var "vo", .var "vl"]) .skip)) := by
  cases kind <;> rfl

/-- Actual output load, wrapping word addition, and permission-checked store. -/
theorem rvv_store_exec (kind : Interpretation) (cfg : Config) (s : State) (output : Address)
    (width : Nat) (acc : List (BitVec 32)) (len : acc.length = width) (cap : width ≤ cfg.capacity)
    (out : s.locals "output" = some (.pointer output))
    (vl : s.locals "vl" = some (.integer width))
    (accum : s.locals (accumulatorName kind) = some (.words32 acc))
    (readable : ∀ a, Footprint output (4*width) a → s.memory.readable a = true)
    (writable : ∀ a, Footprint output (4*width) a → s.memory.writable a = true) :
    Exec cfg (rvvStore kind) s (storeAfter s output width acc) := by
  have load := loadBytes_success s.memory output (4*width) readable
  have readTake : (readWords32 s.memory output width).take width = readWords32 s.memory output width :=
    List.take_of_length_le (by simp)
  have accTake : acc.take width = acc := List.take_of_length_le (by omega)
  have storeTake : (storedWords s.memory output width acc).take width = storedWords s.memory output width acc :=
    List.take_of_length_le (by simp [storedWords_length _ _ _ _ len])
  have store := storeBytes_success s.memory output (encodeWords32 (storedWords s.memory output width acc))
    (by simpa only [encodeWords32_length, storedWords_length _ _ _ _ len] using writable)
  rw [rvv_store_shape]
  apply run_sound (fuel := 6)
  cases kind <;> simp only [accumulatorName] at accum
  all_goals
    simp [run, eval, intrinsic, effect, accumulatorName, update, storeAfter, storedWords,
      out, vl, accum, cap, len, load, decodeWords32_read, readTake, accTake,
      show (List.zipWith (· + ·) (readWords32 s.memory output width) acc).length = width by simp [len],
      show (List.zipWith (· + ·) (readWords32 s.memory output width) acc).take width =
        List.zipWith (· + ·) (readWords32 s.memory output width) acc from storeTake,
      show storeBytes s.memory output (encodeWords32 (List.zipWith (· + ·) (readWords32 s.memory output width) acc)) =
        some (writeBytes s.memory output (encodeWords32 (List.zipWith (· + ·) (readWords32 s.memory output width) acc))) from store]

  all_goals
    funext x
    by_cases h : x = "vo" <;> simp [h]

end Salty.Kernels.Rdsum
