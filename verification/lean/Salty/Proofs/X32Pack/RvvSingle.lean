import Salty.Proofs.X32Pack.RvvPair
import Salty.Proofs.Core.PackingSingleMemory

namespace Salty.Kernels.X32Pack
open CByte

private def branchYes : Stmt → Stmt
  | .branch _ yes _ => yes
  | _ => .skip

def rvvOdd : Stmt := branchYes (firstStatement (dropStatements 3 rvvGroup))
def rvvSingleLoop : Stmt := firstStatement (dropStatements 3 rvvOdd)
def rvvSingleBody : Stmt := loopBody rvvSingleLoop

structure SingleLocals (s : State) (n : Nat) (input output : Address) : Prop where
  count : s.locals "k_2" = some (.integer n)
  input : s.locals "w0" = some (.pointer input)
  output : s.locals "packed_weights" = some (.pointer output)

def rvvSingleAfter (s : State) (n k : Nat) (input output : Address) : State :=
  let t := update s "vl_2" (.integer k)
  let t := update t "vw0_2" (.vector 4 (readBytes s.memory input (4*k)))
  let t := { t with memory := singleResult s.memory input output k }
  let t := update t "w0" (.pointer (input+BitVec.ofNat 64 (4*k)))
  let t := update t "packed_weights" (.pointer (output+BitVec.ofNat 64 (8*k)))
  update t "k_2" (.integer (n-k : Nat))

theorem rvv_single_loop_shape : rvvSingleLoop =
    .loop (.bin .gt (.var "k_2") (.cast .u64 (.lit 0))) rvvSingleBody := rfl

theorem rvv_single_body_shape : rvvSingleBody =
  .seq (.assign "vl_2" (.call .setvl [.var "k_2"]))
  (.seq (.assign "vw0_2" (.call .loadU32RVV [.var "w0", .var "vl_2"]))
  (.seq (.effect .storeStridedU32RVV [.var "packed_weights",
    .cast .i64 (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.lit 4))), .var "vw0_2", .var "vl_2"])
  (.seq (.assign "w0" (.offset 4 (.var "w0") (.var "vl_2")))
  (.seq (.assign "packed_weights" (.offset 4 (.var "packed_weights") (.cast .u64 (.bin .mul (.cast .u64 (.lit 2)) (.var "vl_2")))))
  (.seq (.assign "k_2" (.cast .u64 (.bin .sub (.var "k_2") (.var "vl_2")))) .skip))))) := rfl

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem rvv_single_body_exec (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (loc : SingleLocals s n input output) (bound : 8*n ≤ 2^64)
    (safe : PairSafe s.memory input input output n) :
    Exec cfg rvvSingleBody s (rvvSingleAfter s n (cfg.choose n) input output) := by
  let k := cfg.choose n
  have le : k ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
  have cap : k ≤ cfg.capacity := Nat.le_trans (cfg.bounded n) (Nat.min_le_right ..)
  have load : loadBytes s.memory input (4*k) = some (readBytes s.memory input (4*k)) :=
    loadBytes_success _ _ _ (fun p hp => safe.readA p (footprint_mono (by omega) hp))
  have store : storeStrided32 s.memory output 8 (readBytes s.memory input (4*k)) k =
      some (singleResult s.memory input output k) := by
    apply storeStrided32_success
    · simp
    · intro p hp
      exact safe.writable p (footprint_mono (by omega) (stride8_within output p k hp))
  have sub : convert .u64 ((n : Int)-k) = (n-k : Nat) := cast_sub n k le (by omega)
  have double : convert .u64 (2*(k : Int)) = (2*k : Nat) := by
    simp only [convert, BitVec.toNat_ofInt]
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  have subnorm : max (((n : Int)-k) % 18446744073709551616) 0 = (n-k : Nat) := by simpa [convert] using sub
  have doublenorm : max ((2*(k : Int)) % 18446744073709551616) 0 = (2*k : Nat) := by simpa [convert] using double
  have layout : DisjointStride32 (8#64) k := by
    right
    simp only [BitVec.toNat_ofNat]
    constructor
    · decide
    · omega
  have setCall : intrinsic cfg s.memory .setvl [.integer n] = some (.integer k) := by simp [intrinsic, k]
  have loadCall : intrinsic cfg s.memory .loadU32RVV [.pointer input, .integer k] =
      some (.vector 4 (readBytes s.memory input (4*k))) := by simp [intrinsic, cap, load]
  have storeCall : effect s.memory .storeStridedU32RVV
      [.pointer output, .integer 8, .vector 4 (readBytes s.memory input (4*k)), .integer k] =
      some (singleResult s.memory input output k) := by
    simpa [effect, layout] using store
  have pointer4 : BitVec.ofInt 64 (4*(k : Int)) = BitVec.ofNat 64 (4*k) := by
    rw [show 4*(k : Int) = (4*k : Nat) by omega, BitVec.ofInt_natCast]
  have pointer8 : BitVec.ofInt 64 (4*(2*(k : Int))) = BitVec.ofNat 64 (8*k) := by
    rw [show 4*(2*(k : Int)) = (8*k : Nat) by omega, BitVec.ofInt_natCast]
  rw [rvv_single_body_shape]
  apply run_sound (fuel := 18)
  simp +contextual [run, eval, binary, convert, update_memory, update_locals, loc.count, loc.input, loc.output,
    rvvSingleAfter, subnorm, doublenorm, show max (2 : Int) 0 = 2 by decide, show max (8 : Int) 0 = 8 by decide,
    pointer4, pointer8, setCall, loadCall, storeCall]
  rfl

theorem rvvSingleAfter_memory (s : State) (n k : Nat) (input output : Address) :
    (rvvSingleAfter s n k input output).memory = singleResult s.memory input output k := rfl

theorem rvvSingleAfter_locals (s : State) (n k : Nat) (input output : Address) :
    SingleLocals (rvvSingleAfter s n k input output) (n-k)
      (input+BitVec.ofNat 64 (4*k)) (output+BitVec.ofNat 64 (8*k)) := by
  constructor <;> simp [rvvSingleAfter, update_locals]

/-- The odd-channel scalable loop writes only the first word of each slot,
preserving the holes. The count is unbounded by any evaluator fuel. -/
theorem rvv_single_loop_total (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (loc : SingleLocals s n input output) (bound : 8*n ≤ 2^64)
    (safe : PairSafe s.memory input input output n) :
    ∃ t, Exec cfg rvvSingleLoop s t ∧ t.memory = singleResult s.memory input output n ∧
      SingleLocals t 0 (input+BitVec.ofNat 64 (4*n)) (output+BitVec.ofNat 64 (8*n)) := by
  induction n using Nat.strongRecOn generalizing s input output with
  | ind n ih =>
    by_cases zero : n = 0
    · subst n
      refine ⟨s, ?_, rfl, ?_⟩
      · rw [rvv_single_loop_shape]
        apply Exec.done (v := .integer 0)
        · simp [eval, binary, convert, loc.count]
        · rfl
      · simpa using loc
    · let k := cfg.choose n
      have positive : 0 < k := cfg.positive n (by omega)
      have le : k ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
      let next := rvvSingleAfter s n k input output
      have body : Exec cfg rvvSingleBody s next := rvv_single_body_exec cfg s n input output loc bound safe
      have memory : next.memory = singleResult s.memory input output k := rfl
      have locals := rvvSingleAfter_locals s n k input output
      have nextSafe : PairSafe next.memory (input+BitVec.ofNat 64 (4*k)) (input+BitVec.ofNat 64 (4*k))
          (output+BitVec.ofNat 64 (8*k)) (n-k) := safe.single_advance le
      obtain ⟨t, execution, result, finalLoc⟩ := ih (n-k) (by omega) next
        (input+BitVec.ofNat 64 (4*k)) (output+BitVec.ofNat 64 (8*k)) locals (by omega) nextSafe
      refine ⟨t, ?_, ?_, ?_⟩
      · rw [rvv_single_loop_shape] at execution ⊢
        apply Exec.more (v := .integer 1) (t := next)
        · simp [eval, binary, convert, loc.count, zero]
        · rfl
        · exact body
        · exact execution
      · rw [result, memory, ← singleResult_split safe le]
      · have address (base : Address) (width : Nat) :
            base+BitVec.ofNat 64 (width*k)+BitVec.ofNat 64 (width*(n-k)) = base+BitVec.ofNat 64 (width*n) := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add, show k+(n-k) = n by omega]
        rw [address input 4, address output 8] at finalLoc
        exact finalLoc

end Salty.Kernels.X32Pack
