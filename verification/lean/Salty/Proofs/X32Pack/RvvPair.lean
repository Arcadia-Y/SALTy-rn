import Salty.Proofs.Core.PackingMemory
import Salty.Proofs.Core.CByteSyntax
import Salty.Generated.X32PackRvv

namespace Salty.Kernels.X32Pack
open CByte

def rvvGroups : Stmt := firstStatement (dropStatements 8 Generated.X32Pack.rvv)
def rvvGroup : Stmt := firstStatement (firstStatement rvvGroups)
def rvvChannelLoop : Stmt := firstStatement (dropStatements 2 rvvGroup)
def rvvChannelBody : Stmt := firstStatement (loopBody rvvChannelLoop)
def rvvPairLoop : Stmt := firstStatement (dropStatements 3 rvvChannelBody)
def rvvPairBody : Stmt := loopBody rvvPairLoop

structure PairLocals (s : State) (n : Nat) (a b output : Address) : Prop where
  count : s.locals "k" = some (.integer n)
  left : s.locals "w0" = some (.pointer a)
  right : s.locals "w1" = some (.pointer b)
  output : s.locals "packed_weights" = some (.pointer output)

def rvvPairAfter (s : State) (n k : Nat) (a b output : Address) : State :=
  let left := readBytes s.memory a (4*k)
  let right := readBytes s.memory b (4*k)
  let t := update s "vl" (.integer k)
  let t := update t "vw0" (.vector 4 left)
  let t := update t "vw1" (.vector 4 right)
  let t := update t "vw" (.vectors 4 [left, right])
  let t := { t with memory := pairResult s.memory a b output k }
  let t := update t "w0" (.pointer (a+BitVec.ofNat 64 (4*k)))
  let t := update t "w1" (.pointer (b+BitVec.ofNat 64 (4*k)))
  let t := update t "packed_weights" (.pointer (output+BitVec.ofNat 64 (8*k)))
  update t "k" (.integer (n-k : Nat))

theorem rvv_pair_loop_shape : rvvPairLoop =
    .loop (.bin .gt (.var "k") (.cast .u64 (.lit 0))) rvvPairBody := rfl

theorem rvv_pair_body_shape : rvvPairBody =
  .seq (.assign "vl" (.call .setvl [.var "k"]))
  (.seq (.assign "vw0" (.call .loadU32RVV [.var "w0", .var "vl"]))
  (.seq (.assign "vw1" (.call .loadU32RVV [.var "w1", .var "vl"]))
  (.seq (.assign "vw" (.call .createU32TupleRVV [.var "vw0", .var "vw1"]))
  (.seq (.effect .storeSegment2U32RVV [.var "packed_weights", .var "vw", .var "vl"])
  (.seq (.assign "w0" (.offset 4 (.var "w0") (.var "vl")))
  (.seq (.assign "w1" (.offset 4 (.var "w1") (.var "vl")))
  (.seq (.assign "packed_weights" (.offset 4 (.var "packed_weights") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.var "vl")))))
  (.seq (.assign "k" (.cast .u64 (.bin .sub (.var "k") (.var "vl")))) .skip)))))))) := rfl

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl

private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem rvv_pair_body_exec (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (loc : PairLocals s n a b output) (bound : 8*n ≤ 2^64)
    (safe : PairSafe s.memory a b output n) :
    Exec cfg rvvPairBody s (rvvPairAfter s n (cfg.choose n) a b output) := by
  let k := cfg.choose n
  have le : k ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
  have cap : k ≤ cfg.capacity := Nat.le_trans (cfg.bounded n) (Nat.min_le_right ..)
  have loadA : loadBytes s.memory a (4*k) = some (readBytes s.memory a (4*k)) :=
    loadBytes_success _ _ _ (fun p hp => safe.readA p (footprint_mono (by omega) hp))
  have loadB : loadBytes s.memory b (4*k) = some (readBytes s.memory b (4*k)) :=
    loadBytes_success _ _ _ (fun p hp => safe.readB p (footprint_mono (by omega) hp))
  have store : storeBytes s.memory output (pairBytes s.memory a b k) = some (pairResult s.memory a b output k) := by
    apply storeBytes_success
    intro p hp
    exact safe.writable p (footprint_mono (by simp; omega) hp)
  have sub : convert .u64 ((n : Int)-k) = (n-k : Nat) := cast_sub n k le (by omega)
  have double : convert .u64 (2*(k : Int)) = (2*k : Nat) := by
    simp only [convert, BitVec.toNat_ofInt]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  have subnorm : max (((n : Int)-k) % 18446744073709551616) 0 = (n-k : Nat) := by simpa [convert] using sub
  have doublenorm : max ((2*(k : Int)) % 18446744073709551616) 0 = (2*k : Nat) := by simpa [convert] using double
  have bytesCap : 4*k ≤ 4*cfg.capacity := by omega
  have segmentBound : 8*k ≤ 2^64 := by omega
  simp only [pairBytes, pairResult] at store
  have setCall : intrinsic cfg s.memory .setvl [.integer n] = some (.integer k) := by
    simp [intrinsic, k]
  have leftCall : intrinsic cfg s.memory .loadU32RVV [.pointer a, .integer k] =
      some (.vector 4 (readBytes s.memory a (4*k))) := by simp [intrinsic, cap, loadA]
  have rightCall : intrinsic cfg s.memory .loadU32RVV [.pointer b, .integer k] =
      some (.vector 4 (readBytes s.memory b (4*k))) := by simp [intrinsic, cap, loadB]
  have tupleCall : intrinsic cfg s.memory .createU32TupleRVV
      [.vector 4 (readBytes s.memory a (4*k)), .vector 4 (readBytes s.memory b (4*k))] =
      some (.vectors 4 [readBytes s.memory a (4*k), readBytes s.memory b (4*k)]) := by
    simp [intrinsic, tupleMemoryIntrinsic, readBytes_length, bytesCap]
  have storeCall : effect s.memory .storeSegment2U32RVV
      [.pointer output, .vectors 4 [readBytes s.memory a (4*k), readBytes s.memory b (4*k)], .integer k] =
      some (pairResult s.memory a b output k) := by
    simpa [effect, readBytes_length, segmentBound, pairResult, pairBytes] using store
  have pointer4 : BitVec.ofInt 64 (4*(k : Int)) = BitVec.ofNat 64 (4*k) := by
    rw [show 4*(k : Int) = (4*k : Nat) by omega, BitVec.ofInt_natCast]
  have pointer8 : BitVec.ofInt 64 (4*(2*(k : Int))) = BitVec.ofNat 64 (8*k) := by
    rw [show 4*(2*(k : Int)) = (8*k : Nat) by omega, BitVec.ofInt_natCast]
  rw [rvv_pair_body_shape]
  apply run_sound (fuel := 24)
  simp +contextual [run, eval, binary, convert, update_memory, update_locals, loc.count, loc.left, loc.right, loc.output,
    rvvPairAfter, subnorm, doublenorm, show max (2 : Int) 0 = 2 by decide, pointer4, pointer8, setCall, leftCall, rightCall, tupleCall, storeCall]
  rfl

theorem rvvPairAfter_memory (s : State) (n k : Nat) (a b output : Address) :
    (rvvPairAfter s n k a b output).memory = pairResult s.memory a b output k := rfl

theorem rvvPairAfter_locals (s : State) (n k : Nat) (a b output : Address) :
    PairLocals (rvvPairAfter s n k a b output) (n-k)
      (a+BitVec.ofNat 64 (4*k)) (b+BitVec.ofNat 64 (4*k)) (output+BitVec.ofNat 64 (8*k)) := by
  constructor <;> simp [rvvPairAfter, update_locals]

/-- The actual paired-channel RVV depth loop terminates for arbitrary
progressing VL choices and writes the interleaved original word streams. -/
theorem rvv_pair_loop_total (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (loc : PairLocals s n a b output) (bound : 8*n ≤ 2^64)
    (safe : PairSafe s.memory a b output n) :
    ∃ t, Exec cfg rvvPairLoop s t ∧ t.memory = pairResult s.memory a b output n ∧
      PairLocals t 0 (a+BitVec.ofNat 64 (4*n)) (b+BitVec.ofNat 64 (4*n))
        (output+BitVec.ofNat 64 (8*n)) := by
  induction n using Nat.strongRecOn generalizing s a b output with
  | ind n ih =>
    by_cases zero : n = 0
    · subst n
      refine ⟨s, ?_, ?_, ?_⟩
      · rw [rvv_pair_loop_shape]
        apply Exec.done (v := .integer 0)
        · simp [eval, binary, convert, loc.count]
        · rfl
      · rfl
      · simpa using loc
    · let k := cfg.choose n
      have positive : 0 < k := cfg.positive n (by omega)
      have le : k ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
      let next := rvvPairAfter s n k a b output
      have body : Exec cfg rvvPairBody s next := rvv_pair_body_exec cfg s n a b output loc bound safe
      have memory : next.memory = pairResult s.memory a b output k := rfl
      have locals := rvvPairAfter_locals s n k a b output
      have nextSafe : PairSafe next.memory (a+BitVec.ofNat 64 (4*k)) (b+BitVec.ofNat 64 (4*k))
          (output+BitVec.ofNat 64 (8*k)) (n-k) := safe.advance le (pairBytes s.memory a b k)
      obtain ⟨t, execution, result, finalLoc⟩ := ih (n-k) (by omega) next
        (a+BitVec.ofNat 64 (4*k)) (b+BitVec.ofNat 64 (4*k)) (output+BitVec.ofNat 64 (8*k))
        locals (by omega) nextSafe
      refine ⟨t, ?_, ?_, ?_⟩
      · rw [rvv_pair_loop_shape] at execution ⊢
        apply Exec.more (v := .integer 1) (t := next)
        · simp [eval, binary, convert, loc.count, zero, show (0 : Int) < n by omega]
        · rfl
        · exact body
        · exact execution
      · rw [result, memory, ← pairResult_split safe le]
      · have address (base : Address) (width : Nat) :
            base+BitVec.ofNat 64 (width*k)+BitVec.ofNat 64 (width*(n-k)) =
              base+BitVec.ofNat 64 (width*n) := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add,
            show k+(n-k) = n by omega]
        rw [address a 4, address b 4, address output 8] at finalLoc
        exact finalLoc

end Salty.Kernels.X32Pack
