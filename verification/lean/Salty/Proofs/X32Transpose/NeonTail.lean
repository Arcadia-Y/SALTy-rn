import Salty.Proofs.X32Transpose.NeonRows

namespace Salty.Kernels.X32Transpose
open CByte

def neonTail : Stmt := firstStatement (dropStatements 3 neonOuterBody)

def neonTailBody : Stmt := match neonTail with
  | .branch _ body _ => body
  | _ => .skip

def neonTailPrepared (s : State) (a b : List Byte) : State :=
  let z := bytes32 0
  let t := update s "v1_0_2" (.vector 4 (a ++ b))
  let t := update t "v1_1_2" (.vector 4 (z ++ z))
  let t := update t "v0_0_2" (.vectors 4 [a ++ z, b ++ z])
  let t := update t "v0_low" (.vector 4 (a ++ z))
  update t "v1_low" (.vector 4 (b ++ z))

def neonTailAfter (s : State) (a b : List Byte) (m : Memory) : State :=
  {neonTailPrepared s a b with memory := m}

theorem neon_tail_zero (cfg : Config) (s : State)
    (height : s.locals "bh" = some (.integer 0)) : Exec cfg neonTail s s := by
  apply Exec.no (v := .integer 0)
  · simp [neonTail, neonOuterBody, neonOuter, firstStatement, dropStatements,
      Generated.X32Transpose.neon, eval, binary, height, show convert .u64 0 = 0 by decide]
  · rfl
  · exact .skip

set_option maxHeartbeats 500000 in
/-- The one-row source tail still loads two words, and writes column one
before column zero. Padding and the intermediate store are explicit premises. -/
theorem neon_tail_one (cfg : Config) (s : State) (offset : Nat) (i0 i1 o0 o1 : Address)
    (a b : List Byte) (m1 m2 : Memory) (locals : NeonRowLocals s 1 offset i0 i1 o0 o1)
    (ha : a.length = 4) (hb : b.length = 4)
    (load : loadBytes s.memory i0 8 = some (a ++ b))
    (store1 : storeBytes s.memory o1 b = some m1)
    (store0 : storeBytes m1 o0 a = some m2) :
    Exec cfg neonTail s (neonTailAfter s a b m2) := by
  have hzip := zipU32x2_blocks cfg s.memory a b (bytes32 0) (bytes32 0) ha hb rfl rfl
  have hz : convert .u32 0 = 0 := by decide
  have hone : convert .u64 1 = 1 := by decide
  have hzero : convert .u64 0 = 0 := by decide
  have hand : binary .band (.integer 1) (.integer 1) = some (.integer 1) := by decide
  have prep : Exec cfg (takeStatements 5 neonTailBody) s (neonTailPrepared s a b) := by
    apply run_sound (fuel := 12)
    simp [neonTailBody, neonTail, neonOuterBody, neonOuter, firstStatement, dropStatements,
      takeStatements, Generated.X32Transpose.neon, run, eval, locals.input0, update,
      hz, intrinsic, load, hzip, ha, hb, List.take_left' ha, List.drop_left' ha,
      neonTailPrepared, bytes32]
  have stores : Exec cfg (dropStatements 5 neonTailBody) (neonTailPrepared s a b)
      (neonTailAfter s a b m2) := by
    apply run_sound (fuel := 6)
    simp [neonTailBody, neonTail, neonOuterBody, neonOuter, firstStatement, dropStatements,
      Generated.X32Transpose.neon, run, eval, truth, locals.height, locals.output0,
      locals.output1, update, hone, hand, binary, effect, storeLane, store1, store0,
      ha, hb, List.take_left' ha, List.take_left' hb, neonTailAfter, neonTailPrepared, bytes32]
  apply Exec.yes (v := .integer 1)
  · simp [neonTail, neonOuterBody, neonOuter, firstStatement, dropStatements,
      Generated.X32Transpose.neon, eval, binary, locals.height, hzero]
  · rfl
  · exact exec_take_drop 5 prep stores

theorem neon_tail_alias_result (cfg : Config) (s : State) (offset : Nat)
    (i0 i1 output : Address) (a b : List Byte)
    (locals : NeonRowLocals s 1 offset i0 i1 output output)
    (ha : a.length = 4) (hb : b.length = 4)
    (load : loadBytes s.memory i0 8 = some (a ++ b))
    (safe : ∀ p, Footprint output 4 p → s.memory.writable p = true) :
    ∃ t, Exec cfg neonTail s t ∧ t.memory = writeBytes s.memory output a := by
  let m1 := writeBytes s.memory output b
  let m2 := writeBytes m1 output a
  have hs1 : storeBytes s.memory output b = some m1 := by
    apply storeBytes_success
    simpa only [hb] using safe
  have hs0 : storeBytes m1 output a = some m2 := by
    apply storeBytes_success
    simpa only [m1, writeBytes_writable, ha] using safe
  refine ⟨neonTailAfter s a b m2, neon_tail_one cfg s offset i0 i1 output output a b m1 m2
    locals ha hb load hs1 hs0, ?_⟩
  exact writeBytes_overwrite s.memory output b a (by omega)

end Salty.Kernels.X32Transpose
