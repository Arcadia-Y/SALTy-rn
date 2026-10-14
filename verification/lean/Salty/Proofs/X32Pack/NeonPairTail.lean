import Salty.Proofs.X32Pack.NeonPairLoop

namespace Salty.Kernels.X32Pack
open CByte

theorem neon_pair_tail_body_shape : neonPairTailBody =
  .seq
    (.seq (.assign "v00" (.call .setTupleU32x2 [.var "v00", .lit 0,
      .call .loadLaneU32x2 [.var "w0", .vectorMember (.var "v00") 0, .lit 0]]))
    (.seq (.assign "w0" (.offset 4 (.var "w0") (.lit 1)))
    (.seq (.assign "v00" (.call .setTupleU32x2 [.var "v00", .lit 0,
      .call .loadLaneU32x2 [.var "w1", .vectorMember (.var "v00") 0, .lit 1]]))
    (.seq (.assign "w1" (.offset 4 (.var "w1") (.lit 1)))
    (.seq (.effect .storeU32x2 [.offset 4 (.var "packed_weights") (.lit 0), .vectorMember (.var "v00") 0])
    (.seq (.assign "packed_weights" (.offset 4 (.var "packed_weights") (.lit 2))) .skip))))))
    (.assign "k" (.cast .u64 (.bin .sub (.var "k") (.lit 1)))) := rfl

theorem pairBytes_one (m : Memory) (a b : Address) :
    pairBytes m a b 1 = readBytes m a 4 ++ readBytes m b 4 := by
  simp [pairBytes, interleaveWords, List.take_of_length_le]

def neonPairTailAfter (s : State) (a b output : Address) (x y : List Byte) : State :=
  let xs := readBytes s.memory a 4
  let ys := readBytes s.memory b 4
  let t := update s "v00" (.vectors 4 [replaceWord x xs 0,y])
  let t := update t "w0" (.pointer (a+4))
  let t := update t "v00" (.vectors 4 [xs++ys,y])
  let t := update t "w1" (.pointer (b+4))
  let t := { t with memory := pairResult s.memory a b output 1 }
  let t := update t "packed_weights" (.pointer (output+8))
  update t "k" (.integer 0)

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem neon_pair_tail_body_exec (cfg : Config) (s : State) (a b output : Address) (x y : List Byte)
    (loc : NeonPairLocals s 1 a b output x y) (hx : x.length = 8) (hy : y.length = 8)
    (safe : PairSafe s.memory a b output 1) :
    Exec cfg neonPairTailBody s (neonPairTailAfter s a b output x y) := by
  let xs := readBytes s.memory a 4
  let ys := readBytes s.memory b 4
  have hxs : xs.length = 4 := by simp [xs]
  have hys : ys.length = 4 := by simp [ys]
  have firstLen : (replaceWord x xs 0).length = 8 := replaceWord_length x xs 0 hx hxs (by decide)
  have loadA : loadBytes s.memory a 4 = some xs := loadBytes_success _ _ _ safe.readA
  have loadB : loadBytes s.memory b 4 = some ys := loadBytes_success _ _ _ safe.readB
  have firstLoad : intrinsic cfg s.memory .loadLaneU32x2 [.pointer a, .vector 4 x, .integer 0] =
      some (.vector 4 (replaceWord x xs 0)) := by simp [intrinsic, tupleMemoryIntrinsic, hx, loadA]
  have firstSet : intrinsic cfg s.memory .setTupleU32x2
      [.vectors 4 [x,y], .integer 0, .vector 4 (replaceWord x xs 0)] =
      some (.vectors 4 [replaceWord x xs 0,y]) := by simp [intrinsic, tupleMemoryIntrinsic, hx, hy, firstLen]
  have secondLoad : intrinsic cfg s.memory .loadLaneU32x2
      [.pointer b, .vector 4 (replaceWord x xs 0), .integer 1] = some (.vector 4 (xs++ys)) := by
    simp [intrinsic, tupleMemoryIntrinsic, firstLen, loadB, replaceWord_pair x xs ys hx hxs]
  have secondSet : intrinsic cfg s.memory .setTupleU32x2
      [.vectors 4 [replaceWord x xs 0,y], .integer 0, .vector 4 (xs++ys)] =
      some (.vectors 4 [xs++ys,y]) := by simp [intrinsic, tupleMemoryIntrinsic, firstLen, hy, hxs, hys]
  have store : effect s.memory .storeU32x2 [.pointer output, .vector 4 (xs++ys)] =
      some (pairResult s.memory a b output 1) := by
    have raw := storeBytes_success s.memory output (xs++ys) (by simpa [hxs,hys] using safe.writable)
    simpa [effect, storeVector, hxs, hys, pairResult, pairBytes_one, xs, ys] using raw
  rw [neon_pair_tail_body_shape]
  apply run_sound (fuel := 24)
  simp +contextual [run, eval, binary, convert, update_memory, update_locals,
    loc.count, loc.left, loc.right, loc.output, loc.tuple, firstLoad, firstSet, secondLoad, secondSet, store,
    neonPairTailAfter, xs, ys]

theorem neonPairTailAfter_locals (s : State) (a b output : Address) (x y : List Byte) :
    NeonPairLocals (neonPairTailAfter s a b output x y) 0 (a+4) (b+4) (output+8)
      (readBytes s.memory a 4 ++ readBytes s.memory b 4) y := by
  constructor <;> simp [neonPairTailAfter, update_locals]

theorem neon_pair_tail_total (cfg : Config) (s : State) (r : Nat) (a b output : Address) (x y : List Byte)
    (loc : NeonPairLocals s r a b output x y) (hx : x.length = 8) (hy : y.length = 8)
    (small : r < 2) (safe : PairSafe s.memory a b output r) :
    ∃ t finalX, Exec cfg neonPairTail s t ∧ t.memory = pairResult s.memory a b output r ∧
      NeonPairLocals t 0 (a+BitVec.ofNat 64 (4*r)) (b+BitVec.ofNat 64 (4*r))
        (output+BitVec.ofNat 64 (8*r)) finalX y ∧ finalX.length = 8 := by
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · refine ⟨s, x, ?_, rfl, by simpa using loc, hx⟩
    rw [neon_pair_tail_shape]
    apply Exec.done (v := .integer 0)
    · simp [eval, binary, convert, loc.count]
    · rfl
  · let t := neonPairTailAfter s a b output x y
    have body : Exec cfg neonPairTailBody s t := neon_pair_tail_body_exec cfg s a b output x y loc hx hy safe
    have locals := neonPairTailAfter_locals s a b output x y
    refine ⟨t, readBytes s.memory a 4 ++ readBytes s.memory b 4, ?_, rfl, locals, by simp⟩
    rw [neon_pair_tail_shape]
    apply Exec.more (v := .integer 1) (t := t)
    · simp [eval, binary, convert, loc.count]
    · rfl
    · exact body
    · apply Exec.done (v := .integer 0)
      · have count : t.locals "k" = some (.integer 0) := locals.count
        simp [eval, binary, convert, count]
      · rfl

end Salty.Kernels.X32Pack
