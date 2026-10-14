import Salty.Spec.X32Pack
import Salty.Proofs.X32Pack.ChannelMemory

namespace Salty.Kernels.X32Pack
open CByte

def channelLoop (rvv : Bool) : Stmt := if rvv then rvvChannelLoop else neonChannelLoop

theorem channel_loop_shape (rvv : Bool) : channelLoop rvv =
    .loop (.bin .ge (.var "n") (.cast .u64 (.lit 2)))
      (.seq (pairChannelBody rvv) (.assign "n" (.cast .u64 (.bin .sub (.var "n") (.cast .u64 (.lit 2)))))) := by
  cases rvv <;> rfl

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

/-- Unbounded channel-pair traversal, for either independently extracted body.
The final suffix contract is carried to the optional odd-channel block. -/
theorem channel_loop_total (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (pairs remainder depth extra : Nat) (small : remainder < 2)
    (s : State) (weights bias output : Address)
    (count : s.locals "n" = some (.integer (2*pairs+remainder)))
    (loc : TileLocals s depth extra weights bias output) (tuple : TupleReady rvv s)
    (size : 2*pairs+remainder < 2^64) (bound : 8*depth ≤ 2^64)
    (safe : ChannelSafe s.memory weights bias output (2*pairs+remainder) depth extra) :
    ∃ t, Exec cfg (channelLoop rvv) s t ∧
      t.memory = (packPairs depth extra pairs s.memory weights bias output).memory ∧
      TileEnd t (packPairs depth extra pairs s.memory weights bias output).weights
        (packPairs depth extra pairs s.memory weights bias output).bias
        (packPairs depth extra pairs s.memory weights bias output).output ∧
      t.locals "n" = some (.integer remainder) ∧ TupleReady rvv t ∧
      ChannelSafe t.memory (packPairs depth extra pairs s.memory weights bias output).weights
        (packPairs depth extra pairs s.memory weights bias output).bias
        (packPairs depth extra pairs s.memory weights bias output).output remainder depth extra := by
  induction pairs generalizing s weights bias output with
  | zero =>
    refine ⟨s, ?_, rfl, ⟨loc.weights,loc.bias,loc.output⟩, by simpa using count, tuple, ?_⟩
    · rw [channel_loop_shape]
      apply Exec.done (v := .integer 0)
      · have less : (remainder : Int) < 2 := by omega
        simp [eval, binary, convert, count, less, show max (2 : Int) 0 = 2 by decide]
      · rfl
    · simpa [packPairs] using safe
  | succ pairs ih =>
    have atLeast : 2 ≤ 2*(pairs+1)+remainder := by omega
    obtain ⟨u, tile, uMem, uEnd, uTuple⟩ := pair_tile_total rvv cfg capacity s depth extra weights bias output
      loc tuple bound (safe.pair atLeast)
    let next := update u "n" (.integer (2*pairs+remainder))
    have uCount : u.locals "n" = some (.integer (2*(pairs+1)+remainder)) :=
      (tile.locals_frame "n" (by cases rvv <;> rfl)).trans count
    have subtract : convert .u64 ((2*(pairs+1)+remainder : Nat)- (2 : Int)) = (2*pairs+remainder : Nat) := by
      have h := cast_sub (2*(pairs+1)+remainder) 2 atLeast size
      simpa [show 2*(pairs+1)+remainder-2 = 2*pairs+remainder by omega] using h
    have step : Exec cfg (.assign "n" (.cast .u64 (.bin .sub (.var "n") (.cast .u64 (.lit 2))))) u next := by
      apply Exec.assign
      simp only [eval, uCount, Option.bind_some]
      change some (Value.integer (convert .u64 ((2*(pairs+1)+remainder : Nat) - convert .u64 2))) = _
      rw [show convert .u64 2 = 2 by decide, subtract]
      rfl
    have nextCount : next.locals "n" = some (.integer (2*pairs+remainder)) := by simp [next, update_locals]
    have nextLoc : TileLocals next depth extra (weights+BitVec.ofNat 64 (8*depth)) (nextBias bias true)
        (output+BitVec.ofNat 64 (tileSize depth extra)) := by
      constructor
      · rw [show next.locals "kc" = u.locals "kc" by simp [next, update_locals],
          tile.locals_frame "kc" (by cases rvv <;> rfl)]
        exact loc.depth
      · rw [show next.locals "extra_bytes" = u.locals "extra_bytes" by simp [next, update_locals],
          tile.locals_frame "extra_bytes" (by cases rvv <;> rfl)]
        exact loc.extra
      · simpa [next, update_locals] using uEnd.weights
      · simpa [next, update_locals] using uEnd.bias
      · simpa [next, update_locals] using uEnd.output
    have nextTuple : TupleReady rvv next := uTuple.of_frame (by simp [next, update_locals])
    have nextSafe : ChannelSafe next.memory (weights+BitVec.ofNat 64 (8*depth)) (nextBias bias true)
        (output+BitVec.ofNat 64 (tileSize depth extra)) (2*pairs+remainder) depth extra := by
      rw [show next.memory = u.memory by rfl, uMem]
      apply ChannelSafe.advance_pair
      simpa [show 2*pairs+remainder+2 = 2*(pairs+1)+remainder by omega] using safe
    obtain ⟨t, loop, tMem, tEnd, tCount, tTuple, tSafe⟩ := ih next _ _ _ nextCount nextLoc nextTuple (by omega) nextSafe
    have model : packPairs depth extra (pairs+1) s.memory weights bias output =
        packPairs depth extra pairs next.memory (weights+BitVec.ofNat 64 (8*depth)) (nextBias bias true)
          (output+BitVec.ofNat 64 (tileSize depth extra)) := by
      simp only [packPairs, next, update_memory, uMem]
    refine ⟨t, ?_, ?_, ?_, tCount, tTuple, ?_⟩
    · rw [channel_loop_shape] at loop ⊢
      apply Exec.more (v := .integer 1) (t := next)
      · have ge : (2*(pairs+1)+remainder : Nat) ≥ (2 : Int) := by omega
        simp [eval, binary, convert, count, ge, show max (2 : Int) 0 = 2 by decide]
        omega
      · rfl
      · exact .seq tile step
      · exact loop
    · rw [model]; exact tMem
    · rw [model]; exact tEnd
    · rw [model]; exact tSafe

end Salty.Kernels.X32Pack
