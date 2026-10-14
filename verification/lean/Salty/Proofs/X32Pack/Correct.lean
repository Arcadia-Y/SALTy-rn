import Salty.Proofs.X32Pack.Groups
import Salty.Proofs.Core.CByteMachine

namespace Salty.Kernels.X32Pack
open CByte

theorem Entry.productBound {s : State} {c : Call} (entry : Entry s c) : c.channels*c.depth < 2^64 := by
  have count : 1 ≤ 4*c.groups := by have := entry.groupsPositive; omega
  have h := Nat.mul_le_mul_right (c.channels*c.depth) count
  simp only [Nat.one_mul] at h
  have product : 4*c.groups*(c.channels*c.depth) = 4*c.groups*c.channels*c.depth := by ac_rfl
  rw [product] at h
  have bound := entry.weightsBound
  omega

theorem Entry.depthBound {s : State} {c : Call} (entry : Entry s c) : 8*c.depth ≤ 2^64 := by
  have tileCount : 1 ≤ tiles c.channels := by have := entry.channelsPositive; unfold tiles; omega
  have groupCount : 1 ≤ c.groups := by have := entry.groupsPositive; omega
  have counts : 1 ≤ c.groups*tiles c.channels := by
    have h := Nat.mul_le_mul groupCount tileCount
    simpa using h
  have output := Nat.mul_le_mul_right (tileSize c.depth c.extra) counts
  simp only [Nat.one_mul] at output
  change tileSize c.depth c.extra ≤ outputSize c at output
  have base : 8*c.depth ≤ tileSize c.depth c.extra := by simp [tileSize]; omega
  have bound := entry.outputBound
  omega

def program (rvv : Bool) : Stmt := if rvv then Generated.X32Pack.rvv else Generated.X32Pack.neon
def initialized (rvv : Bool) (s : State) : State := if rvv then s else neonInitialized s

theorem init_exec (rvv : Bool) (cfg : Config) (s : State) (c : Call) (entry : Entry s c) :
    Exec cfg (takeStatements (if rvv then 8 else 11) (program rvv)) s (initialized rvv s) := by
  cases rvv with
  | true => exact assertions_exec cfg s c entry
  | false => exact neon_init_exec cfg s c entry

theorem initialized_entry (rvv : Bool) (s : State) (c : Call) (entry : Entry s c) : Entry (initialized rvv s) c := by
  cases rvv with
  | true => exact entry
  | false => exact neonInitialized_entry s c entry

theorem initialized_memory (rvv : Bool) (s : State) : (initialized rvv s).memory = s.memory := by
  cases rvv <;> rfl

theorem initialized_tuple (rvv : Bool) (s : State) : TupleReady rvv (initialized rvv s) := by
  cases rvv with
  | true => trivial
  | false => exact ⟨List.replicate 8 0,List.replicate 8 0,by rfl,by simp,by simp⟩

/-- Complete execution of either actual extracted kernel. Every loop is
unbounded; the scalar tile reference observes all memory bytes and permissions. -/
theorem correct (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity) (s : State) (c : Call) (entry : Entry s c) :
    ∃ t, Exec cfg (program rvv) s t ∧
      t.memory = packGroups c.channels c.depth c.extra c.groups s.memory c.weights c.bias c.output := by
  let u := initialized rvv s
  have init : Exec cfg (takeStatements (if rvv then 8 else 11) (program rvv)) s u := init_exec rvv cfg s c entry
  have h : Entry u c := initialized_entry rvv s c entry
  have loc : GroupLocals u c.channels c.depth c.extra c.weights c.bias c.output :=
    ⟨h.channels,h.depth,h.extra,h.weights,h.bias,h.output⟩
  obtain ⟨t, groups, result⟩ := groups_total rvv cfg capacity c.groups c.channels c.depth c.extra u c.weights c.bias c.output
    h.groups loc (initialized_tuple rvv s) h.groupsPositive h.groupsSize h.channelsSize h.depthPositive h.depthBound h.productBound h.groupSafe
  refine ⟨t, ?_, ?_⟩
  · apply exec_take_drop (if rvv then 8 else 11) init
    cases rvv <;> exact .seq groups .skip
  · simpa only [u, initialized_memory] using result

/-- Independent source and target executions reach identical complete memory,
including untouched holes, byte gaps, and access permissions. -/
theorem extracted_equivalent (cfg : Config) (c : Call) (capacity : 8 ≤ cfg.capacity) :
    CByte.Equivalent cfg Generated.X32Pack.neon Generated.X32Pack.rvv (fun s => Entry s c) := by
  intro s entry
  obtain ⟨a, ha, hma⟩ := correct false cfg capacity s c entry
  obtain ⟨b, hb, hmb⟩ := correct true cfg capacity s c entry
  exact ⟨a,b,ha,hb,hma.trans hmb.symm⟩

/-- Whole-function common return/fault/divergence equivalence for every
bounded progressing RVV vector-length schedule and every admitted call. -/
theorem behavior_equivalent_proof (cfg : Config) (c : Call) (capacity : 8 ≤ cfg.capacity) :
    Salty.Equivalent (CByte.machine cfg) (CByte.machine cfg)
      (fun s => ⟨[Generated.X32Pack.neon],s⟩)
      (fun s => ⟨[Generated.X32Pack.rvv],s⟩) (fun s => Entry s c) :=
  (extracted_equivalent cfg c capacity).behavior

end Salty.Kernels.X32Pack
