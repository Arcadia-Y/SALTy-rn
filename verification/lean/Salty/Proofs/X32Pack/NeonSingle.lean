import Salty.Proofs.X32Pack.NeonPair
import Salty.Proofs.X32Pack.RvvSingle
import Salty.Proofs.Core.CWordCodec

set_option maxRecDepth 4096

namespace Salty.Kernels.X32Pack
open CByte

private def yesBranch : Stmt → Stmt
  | .branch _ yes _ => yes
  | _ => .skip

def neonOdd : Stmt := yesBranch (firstStatement (dropStatements 3 neonGroup))
def neonSingleDepth : Stmt := firstStatement (dropStatements 3 neonOdd)
def neonSingleBody : Stmt := firstStatement neonSingleDepth
def neonSingleLoop : Stmt := dropStatements 1 neonSingleDepth

def neonSingleAfter (s : State) (n : Nat) (input output : Address) : State :=
  let t := { s with memory := singleResult s.memory input output 1 }
  let t := update t "w0" (.pointer (input+4))
  let t := update t "packed_weights" (.pointer (output+8))
  update t "k_2" (.integer (n-1 : Nat))

theorem neon_single_loop_shape : neonSingleLoop = .loop (.bin .ne (.var "k_2") (.lit 0)) neonSingleBody := rfl

theorem neon_single_depth_shape : neonSingleDepth = .seq neonSingleBody neonSingleLoop := rfl

theorem neon_single_body_shape : neonSingleBody =
  .seq
    (.seq
      (.seq (.effect .storeU32 [.var "packed_weights", .cast .u32 (.param (.var "w0") 0)])
        (.assign "w0" (.offset 4 (.var "w0") (.lit 1))))
      (.seq (.assign "packed_weights" (.offset 4 (.var "packed_weights") (.lit 2))) .skip))
    (.assign "k_2" (.cast .u64 (.bin .sub (.var "k_2") (.lit 1)))) := rfl

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

set_option maxRecDepth 4096 in
theorem neon_single_body_exec (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (loc : SingleLocals s n input output) (positive : 0 < n) (bound : 8*n ≤ 2^64)
    (safe : PairSafe s.memory input input output n) :
    Exec cfg neonSingleBody s (neonSingleAfter s n input output) := by
  obtain ⟨value, load, bytes, lo, hi⟩ := unsigned_load_roundtrip s.memory input
    (fun p hp => safe.readA p (footprint_mono (by omega) hp))
  have store : effect s.memory .storeU32 [.pointer output, .integer (convert .u32 value)] =
      some (singleResult s.memory input output 1) := by
    have raw := storeBytes_success s.memory output (readBytes s.memory input 4)
      (fun p hp => safe.writable p (footprint_mono (by simp; omega) hp))
    have upper : convert .u32 value < 4294967296 := hi
    have take : (readBytes s.memory input 4).take 4 = readBytes s.memory input 4 := List.take_of_length_le (by simp)
    simpa [effect, lo, upper, bytes, singleResult, writeStrided32, take] using raw
  have sub : convert .u64 ((n : Int)-1) = (n-1 : Nat) := cast_sub n 1 (by omega) (by omega)
  let written : State := { s with memory := singleResult s.memory input output 1 }
  let advanced := update written "w0" (.pointer (input+4))
  let advancedOut := update advanced "packed_weights" (.pointer (output+8))
  have copy : Exec cfg (.effect .storeU32 [.var "packed_weights", .cast .u32 (.param (.var "w0") 0)]) s written := by
    apply Exec.effect (vs := [.pointer output, .integer (convert .u32 value)])
    · simp [eval, loc.input, loc.output, load]
    · exact store
  have inputStep : Exec cfg (.assign "w0" (.offset 4 (.var "w0") (.lit 1))) written advanced := by
    apply Exec.assign
    simp [eval, written, loc.input]
  have outputStep : Exec cfg (.assign "packed_weights" (.offset 4 (.var "packed_weights") (.lit 2))) advanced advancedOut := by
    apply Exec.assign
    simp [eval, advanced, written, update_locals, loc.output]
  have countStep : Exec cfg (.assign "k_2" (.cast .u64 (.bin .sub (.var "k_2") (.lit 1)))) advancedOut
      (neonSingleAfter s n input output) := by
    apply Exec.assign
    simp [eval, binary, advancedOut, advanced, written, update_locals, loc.count, sub]
  rw [neon_single_body_shape]
  exact .seq (.seq (.seq copy inputStep) (.seq outputStep .skip)) countStep

theorem neonSingleAfter_locals (s : State) (n : Nat) (input output : Address) :
    SingleLocals (neonSingleAfter s n input output) (n-1) (input+4) (output+8) := by
  constructor <;> simp [neonSingleAfter, update_locals]

/-- The continuation loop of the source do/while traversal. -/
theorem neon_single_loop_total (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (loc : SingleLocals s n input output) (bound : 8*n ≤ 2^64)
    (safe : PairSafe s.memory input input output n) :
    ∃ t, Exec cfg neonSingleLoop s t ∧ t.memory = singleResult s.memory input output n ∧
      SingleLocals t 0 (input+BitVec.ofNat 64 (4*n)) (output+BitVec.ofNat 64 (8*n)) := by
  induction n using Nat.strongRecOn generalizing s input output with
  | ind n ih =>
    by_cases zero : n = 0
    · subst n
      refine ⟨s, ?_, rfl, by simpa using loc⟩
      rw [neon_single_loop_shape]
      apply Exec.done (v := .integer 0)
      · simp [eval, binary, loc.count]
      · rfl
    · let next := neonSingleAfter s n input output
      have body : Exec cfg neonSingleBody s next := neon_single_body_exec cfg s n input output loc (by omega) bound safe
      have memory : next.memory = singleResult s.memory input output 1 := rfl
      have locals := neonSingleAfter_locals s n input output
      have nextSafe : PairSafe next.memory (input+4) (input+4) (output+8) (n-1) := safe.single_advance (by omega)
      obtain ⟨t, execution, result, finalLoc⟩ := ih (n-1) (by omega) next (input+4) (output+8) locals (by omega) nextSafe
      refine ⟨t, ?_, ?_, ?_⟩
      · rw [neon_single_loop_shape] at execution ⊢
        apply Exec.more (v := .integer 1) (t := next)
        · simp [eval, binary, loc.count, zero]
        · rfl
        · exact body
        · exact execution
      · rw [result, memory]
        exact (singleResult_split safe (show 1 ≤ n by omega)).symm
      · have address (base : Address) (width : Nat) :
            base+BitVec.ofNat 64 width+BitVec.ofNat 64 (width*(n-1)) = base+BitVec.ofNat 64 (width*n) := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          have h : width + width*(n-1) = width*n := by
            have count : 1+(n-1) = n := by omega
            simpa only [Nat.mul_add, Nat.mul_one] using congrArg (fun j => width*j) count
          rw [h]
        change SingleLocals t 0
          (input+BitVec.ofNat 64 4+BitVec.ofNat 64 (4*(n-1)))
          (output+BitVec.ofNat 64 8+BitVec.ofNat 64 (8*(n-1))) at finalLoc
        rw [address input 4, address output 8] at finalLoc
        exact finalLoc

/-- The source executes the first scalar copy unconditionally, so this complete
do/while theorem explicitly requires positive depth. -/
theorem neon_single_depth_total (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (loc : SingleLocals s n input output) (positive : 0 < n) (bound : 8*n ≤ 2^64)
    (safe : PairSafe s.memory input input output n) :
    ∃ t, Exec cfg neonSingleDepth s t ∧ t.memory = singleResult s.memory input output n ∧
      SingleLocals t 0 (input+BitVec.ofNat 64 (4*n)) (output+BitVec.ofNat 64 (8*n)) := by
  obtain ⟨t, execution, memory, locals⟩ := neon_single_loop_total cfg s n input output loc bound safe
  rw [neon_single_loop_shape] at execution
  cases execution with
  | done evaluated falsity =>
    have trueEval : eval cfg s (.bin .ne (.var "k_2") (.lit 0)) = some (.integer 1) := by
      simp [eval, binary, loc.count, show n ≠ 0 by omega]
    rw [trueEval] at evaluated
    cases evaluated
    contradiction
  | more evaluated truth body rest =>
    refine ⟨t, ?_, memory, locals⟩
    rw [neon_single_depth_shape]
    exact .seq body (by simpa only [neon_single_loop_shape] using rest)

end Salty.Kernels.X32Pack
