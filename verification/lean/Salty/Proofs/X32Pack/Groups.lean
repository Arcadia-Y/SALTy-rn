import Salty.Spec.X32Pack
import Salty.Proofs.X32Pack.Group

namespace Salty.Kernels.X32Pack
open CByte

def groupsProgram (rvv : Bool) : Stmt := if rvv then rvvGroups else neonGroups
def groupsBody (rvv : Bool) : Stmt := firstStatement (groupsProgram rvv)
def groupsLoop (rvv : Bool) : Stmt := dropStatements 1 (groupsProgram rvv)

theorem groups_body_shape (rvv : Bool) : groupsBody rvv =
    .seq (groupProgram rvv) (.assign "g" (.cast .u64 (.bin .sub (.var "g") (.lit 1)))) := by cases rvv <;> rfl

theorem groups_loop_shape (rvv : Bool) : groupsLoop rvv =
    .loop (.bin .ne (.var "g") (.lit 0)) (groupsBody rvv) := by cases rvv <;> rfl

theorem groups_program_shape (rvv : Bool) : groupsProgram rvv = .seq (groupsBody rvv) (groupsLoop rvv) := by
  cases rvv <;> rfl

private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

/-- Arbitrarily many complete groups, with independently extracted source and
target group bodies. The only count restriction is the caller's size_t bound. -/
theorem groups_loop_total (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (groups channels depth extra : Nat) (s : State) (weights bias output : Address)
    (count : s.locals "g" = some (.integer groups))
    (loc : GroupLocals s channels depth extra weights bias output) (tuple : TupleReady rvv s)
    (groupsSize : groups < 2^64) (channelsSize : channels < 2^64) (positive : 0 < depth)
    (depthBound : 8*depth ≤ 2^64) (productBound : channels*depth < 2^64)
    (safe : GroupSafe s.memory weights bias output groups channels depth extra) :
    ∃ t, Exec cfg (groupsLoop rvv) s t ∧
      t.memory = packGroups channels depth extra groups s.memory weights bias output := by
  induction groups generalizing s weights bias output with
  | zero =>
    refine ⟨s, ?_, rfl⟩
    rw [groups_loop_shape]
    apply Exec.done (v := .integer 0)
    · simp [eval, binary, count]
    · rfl
  | succ groups ih =>
    obtain ⟨u, group, uMem, uLoc, uTuple⟩ := group_total rvv cfg capacity channels depth extra s weights bias output
      loc tuple channelsSize positive depthBound productBound (safe.channel (by omega))
    let next := update u "g" (.integer groups)
    have uCount : u.locals "g" = some (.integer (groups+1 : Nat)) :=
      (group.locals_frame "g" (by cases rvv <;> rfl)).trans count
    have subtract : convert .u64 ((groups+1 : Nat)-(1 : Int)) = groups := by
      have h := cast_sub (groups+1) 1 (by omega) groupsSize
      simpa using h
    have step : Exec cfg (.assign "g" (.cast .u64 (.bin .sub (.var "g") (.lit 1)))) u next := by
      apply Exec.assign
      simp only [eval, uCount, binary, Option.bind_some, pure, bind, subtract]
    have nextCount : next.locals "g" = some (.integer groups) := by simp [next, update_locals]
    have nextLoc : GroupLocals next channels depth extra
        (weights+BitVec.ofNat 64 (weightBytes channels depth)) (biasAdvance bias channels)
        (output+BitVec.ofNat 64 (groupBytes channels depth extra)) := by
      constructor <;> simp [next, update_locals, uLoc.channels, uLoc.depth, uLoc.extra, uLoc.weights, uLoc.bias, uLoc.output]
    have nextTuple := uTuple.of_frame (show next.locals "v00" = u.locals "v00" by simp [next, update_locals])
    have nextSafe : GroupSafe next.memory (weights+BitVec.ofNat 64 (weightBytes channels depth)) (biasAdvance bias channels)
        (output+BitVec.ofNat 64 (groupBytes channels depth extra)) groups channels depth extra := by
      change GroupSafe u.memory _ _ _ _ _ _ _
      rw [uMem]
      exact safe.advance_group
    obtain ⟨t, loop, result⟩ := ih next _ _ _ nextCount nextLoc nextTuple (by omega) nextSafe
    refine ⟨t, ?_, ?_⟩
    · rw [groups_loop_shape] at loop ⊢
      apply Exec.more (v := .integer 1) (t := next)
      · simp [eval, binary, count]
        omega
      · rfl
      · rw [groups_body_shape]; exact .seq group step
      · exact loop
    · rw [result]
      change packGroups channels depth extra groups u.memory _ _ _ = _
      rw [uMem]
      rfl

/-- Actual outer do/while: positivity justifies its mandatory first group. -/
theorem groups_total (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (groups channels depth extra : Nat) (s : State) (weights bias output : Address)
    (count : s.locals "g" = some (.integer groups))
    (loc : GroupLocals s channels depth extra weights bias output) (tuple : TupleReady rvv s)
    (groupsPositive : 0 < groups) (groupsSize : groups < 2^64) (channelsSize : channels < 2^64)
    (positive : 0 < depth) (depthBound : 8*depth ≤ 2^64) (productBound : channels*depth < 2^64)
    (safe : GroupSafe s.memory weights bias output groups channels depth extra) :
    ∃ t, Exec cfg (groupsProgram rvv) s t ∧
      t.memory = packGroups channels depth extra groups s.memory weights bias output := by
  obtain ⟨t, execution, memory⟩ := groups_loop_total rvv cfg capacity groups channels depth extra s weights bias output
    count loc tuple groupsSize channelsSize positive depthBound productBound safe
  refine ⟨t, ?_, memory⟩
  rw [groups_loop_shape] at execution
  cases execution with
  | done he ht =>
    have nonzero : groups ≠ 0 := by omega
    simp [eval, binary, count, nonzero] at he
    subst_vars
    contradiction
  | more he ht body rest =>
    rw [groups_program_shape, groups_loop_shape]
    exact .seq body rest

end Salty.Kernels.X32Pack
