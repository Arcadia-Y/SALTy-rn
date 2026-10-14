import Salty.Spec.X32Pack
import Salty.Proofs.X32Pack.ChannelLoop

namespace Salty.Kernels.X32Pack
open CByte

def channelsProgram (rvv : Bool) : Stmt :=
  takeStatements 2 (dropStatements 2 (if rvv then rvvGroup else neonGroup))

theorem channels_program_shape (rvv : Bool) : channelsProgram rvv =
  .seq (channelLoop rvv)
    (.seq (.branch (.bin .ne (.var "n") (.cast .u64 (.lit 0))) (oddChannelBody rvv) .skip) .skip) := by
  cases rvv <;> rfl

/-- Both actual channel traversals implement the same complete tile fold,
including the optional final odd channel. No channel count bound is used as fuel. -/
theorem channels_total (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (channels depth extra : Nat) (s : State) (weights bias output : Address)
    (count : s.locals "n" = some (.integer channels))
    (loc : TileLocals s depth extra weights bias output) (tuple : TupleReady rvv s)
    (size : channels < 2^64) (positive : 0 < depth) (bound : 8*depth ≤ 2^64)
    (safe : ChannelSafe s.memory weights bias output channels depth extra) :
    ∃ t, Exec cfg (channelsProgram rvv) s t ∧
      t.memory = (packChannels s.memory weights bias output channels depth extra).memory ∧
      TileEnd t (packChannels s.memory weights bias output channels depth extra).weights
        (packChannels s.memory weights bias output channels depth extra).bias
        (packChannels s.memory weights bias output channels depth extra).output ∧ TupleReady rvv t := by
  have partition : 2*(channels/2)+channels%2 = channels := by omega
  have loopCount : s.locals "n" = some (.integer (2*(channels/2)+channels%2 : Nat)) := by rw [partition]; exact count
  have loopSafe : ChannelSafe s.memory weights bias output (2*(channels/2)+channels%2) depth extra := by rw [partition]; exact safe
  obtain ⟨u, loop, uMem, uEnd, uCount, uTuple, uSafe⟩ := channel_loop_total rvv cfg capacity
    (channels/2) (channels%2) depth extra (by omega) s weights bias output loopCount loc tuple (by omega) bound loopSafe
  let result := packPairs depth extra (channels/2) s.memory weights bias output
  have locU : TileLocals u depth extra result.weights result.bias result.output := by
    constructor
    · rw [loop.locals_frame "kc" (by cases rvv <;> rfl)]; exact loc.depth
    · rw [loop.locals_frame "extra_bytes" (by cases rvv <;> rfl)]; exact loc.extra
    · exact uEnd.weights
    · exact uEnd.bias
    · exact uEnd.output
  by_cases even : channels%2 = 0
  · refine ⟨u, ?_, ?_, ?_, uTuple⟩
    · rw [channels_program_shape]
      refine .seq loop (.seq ?_ .skip)
      apply Exec.no (v := .integer 0)
      · simp [eval, binary, convert, uCount, even]
      · rfl
      · exact .skip
    · simpa [packChannels, even] using uMem
    · simpa [packChannels, even] using uEnd
  · have odd : channels%2 = 1 := by omega
    have safeOdd : ChannelSafe u.memory result.weights result.bias result.output 1 depth extra := by
      simpa [odd] using uSafe
    obtain ⟨v, tile, vMem, vEnd, vTuple⟩ := odd_tile_total rvv cfg capacity u depth extra
      result.weights result.bias result.output locU uTuple positive bound safeOdd.odd
    refine ⟨v, ?_, ?_, ?_, vTuple⟩
    · rw [channels_program_shape]
      refine .seq loop (.seq ?_ .skip)
      apply Exec.yes (v := .integer 1)
      · simp [eval, binary, convert, uCount, odd]
      · rfl
      · exact tile
    · rw [vMem, uMem]
      simp [packChannels, even, oddResult, result]
    · simpa [packChannels, even, oddResult, result] using vEnd

end Salty.Kernels.X32Pack
