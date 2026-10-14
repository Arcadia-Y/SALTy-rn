import Salty.Proofs.X32Pack.Headers
import Salty.Proofs.X32Pack.SpecLemmas

namespace Salty.Kernels.X32Pack
open CByte

def assertions : Stmt := takeStatements 8 Generated.X32Pack.rvv

theorem neon_assertions_shape : takeStatements 8 Generated.X32Pack.neon = assertions := rfl

theorem assertions_exec (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    Exec cfg assertions s s := by
  have hg : c.groups ≠ 0 := by have := h.groupsPositive; omega
  have hn : c.channels ≠ 0 := by have := h.channelsPositive; omega
  have hk : c.depth ≠ 0 := by have := h.depthPositive; omega
  have hw : c.weights ≠ 0#64 := h.weightsNonzero
  have ho : c.output ≠ 0#64 := h.outputNonzero
  apply run_sound (fuel := 20)
  simp [assertions, takeStatements, Generated.X32Pack.rvv, run, eval, truth, binary, convert,
    effect, h.groups, h.channels, h.depth, h.nr, h.kr, h.sr, h.weights, h.output, hg, hn, hk, hw, ho, show max (2 : Int) 0 = 2 by decide, show max (1 : Int) 0 = 1 by decide]

def neonInitialized (s : State) : State := update s "v00" (.vectors 4 [List.replicate 8 0, List.replicate 8 0])

theorem neon_tuple_init (cfg : Config) (s : State) :
    Exec cfg (takeStatements 3 (dropStatements 8 Generated.X32Pack.neon)) s (neonInitialized s) := by
  apply run_sound (fuel := 8)
  simp +contextual [takeStatements, dropStatements, Generated.X32Pack.neon, run, eval, intrinsic, tupleMemoryIntrinsic,
    convert, update, neonInitialized, bytes32]

theorem neon_init_exec (cfg : Config) (s : State) (c : Call) (h : Entry s c) :
    Exec cfg (takeStatements 11 Generated.X32Pack.neon) s (neonInitialized s) := by
  apply exec_take_drop 8
  · exact assertions_exec cfg s c h
  · exact neon_tuple_init cfg s

theorem neonInitialized_entry (s : State) (c : Call) (h : Entry s c) : Entry (neonInitialized s) c := by
  cases h
  constructor <;> first | assumption | simpa [neonInitialized, update] using (by assumption)

end Salty.Kernels.X32Pack
