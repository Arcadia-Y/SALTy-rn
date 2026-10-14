import Salty.Proofs.Core.CReduction
import Salty.Proofs.Core.CByteSyntax
import Salty.Proofs.Core.CByteMemory
import Salty.Generated.QS8RsumRvv
import Salty.Generated.QU8RsumRvv

namespace Salty.Kernels.Rsum
open CByte ReductionISA

def rvvProgram : Interpretation → Stmt
  | .signed => Generated.QS8Rsum.rvv
  | .unsigned => Generated.QU8Rsum.rvv

def rvvLoop (kind : Interpretation) : Stmt := firstStatement (dropStatements 6 (rvvProgram kind))
def rvvBody (kind : Interpretation) : Stmt := loopBody (rvvLoop kind)

structure RvvLocals (s : State) (n : Nat) (input output : Address) (capacity : Nat)
    (acc : List (BitVec 32)) : Prop where
  batch : s.locals "batch" = some (.integer n)
  inputPtr : s.locals "input" = some (.pointer input)
  outputPtr : s.locals "output" = some (.pointer output)
  vlmax : s.locals "vlmax" = some (.integer capacity)
  vacc : s.locals "vacc" = some (.words32 acc)

def rvvBodyAfter (kind : Interpretation) (s : State) (n k : Nat) (input : Address)
    (acc : List (BitVec 32)) (xs : List Byte) : State :=
  let t := update s "vl" (.integer k)
  let t := update t "vt" (.vector 1 xs)
  match kind with
  | .signed =>
    let t := update t "vt32" (.words32 (widen32 kind xs))
    let t := update t "vacc" (.words32 (addPrefix acc (widen32 kind xs)))
    let t := update t "input" (.pointer (input + BitVec.ofNat 64 k))
    update t "batch" (.integer (n - k : Nat))
  | .unsigned =>
    let t := update t "input" (.pointer (input + BitVec.ofNat 64 k))
    let t := update t "batch" (.integer (n - k : Nat))
    let t := update t "vt32" (.words32 (widen32 kind xs))
    update t "vacc" (.words32 (addPrefix acc (widen32 kind xs)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem rvv_body_exec (cfg : Config) (kind : Interpretation) (s : State) (n : Nat)
    (input output : Address) (acc : List (BitVec 32)) (xs : List Byte)
    (loc : RvvLocals s n input output cfg.capacity acc) (bound : n < 2^64)
    (ha : acc.length = cfg.capacity) (hx : xs.length = cfg.choose n)
    (load : loadBytes s.memory input (cfg.choose n) = some xs) :
    Exec cfg (rvvBody kind) s (rvvBodyAfter kind s n (cfg.choose n) input acc xs) := by
  have le : cfg.choose n ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
  have cap : cfg.choose n ≤ cfg.capacity := Nat.le_trans (cfg.bounded n) (Nat.min_le_right ..)
  have takeXs : xs.take (cfg.choose n) = xs := by rw [← hx]; exact List.take_length
  have sub : convert .u64 ((n : Int) - cfg.choose n) = (n - cfg.choose n : Nat) := cast_sub n (cfg.choose n) le bound
  have subnorm : max (((n : Int) - cfg.choose n) % 18446744073709551616) 0 = (n - cfg.choose n : Nat) := by
    simpa [convert] using sub
  cases kind <;> apply run_sound (fuel := 20) <;>
    simp +contextual [rvvBody, rvvLoop, rvvProgram, Generated.QS8Rsum.rvv, Generated.QU8Rsum.rvv,
      firstStatement, dropStatements, loopBody, run, eval, intrinsic, reductionIntrinsic,
      saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic, unsignedArithmeticIntrinsic,
      binary, convert, loc.batch, loc.inputPtr, loc.vacc, load, update,
      rvvBodyAfter, hx, ha, cap, takeXs, widen32, addPrefix, sub, subnorm] <;>
    simp only [← List.map_take, takeXs]

theorem rvvBodyAfter_memory (kind : Interpretation) (s : State) (n k : Nat) (input : Address)
    (acc : List (BitVec 32)) (xs : List Byte) :
    (rvvBodyAfter kind s n k input acc xs).memory = s.memory := by cases kind <;> rfl

theorem rvvBodyAfter_locals (kind : Interpretation) (s : State) (n k : Nat) (input output : Address)
    (capacity : Nat) (acc : List (BitVec 32)) (xs : List Byte)
    (loc : RvvLocals s n input output capacity acc) :
    RvvLocals (rvvBodyAfter kind s n k input acc xs) (n-k) (input + BitVec.ofNat 64 k)
      output capacity (addPrefix acc (widen32 kind xs)) := by
  cases kind <;> constructor <;> simp [rvvBodyAfter, update, loc.outputPtr, loc.vlmax]

theorem rvv_loop_shape (kind : Interpretation) :
    rvvLoop kind = .loop (.bin .gt (.var "batch") (.cast .u64 (.lit 0))) (rvvBody kind) := by
  cases kind <;> rfl

/-- The actual extracted scalable loop terminates for every progressing,
bounded VL choice, preserving all memory and the total modular 32-bit sum. -/
theorem rvv_loop_total (cfg : Config) (kind : Interpretation) (s : State) (n : Nat)
    (input output : Address) (acc : List (BitVec 32))
    (loc : RvvLocals s n input output cfg.capacity acc) (bound : n < 2^64)
    (ha : acc.length = cfg.capacity)
    (readable : ∀ a, Footprint input n a → s.memory.readable a = true) :
    ∃ t final, Exec cfg (rvvLoop kind) s t ∧ t.memory = s.memory ∧
      RvvLocals t 0 (input + BitVec.ofNat 64 n) output cfg.capacity final ∧
      final.length = cfg.capacity ∧
      sumWords final = sumWords acc + sumWords (widen32 kind (readBytes s.memory input n)) := by
  by_cases zero : n = 0
  · subst n
    refine ⟨s, acc, ?_, rfl, ?_, ha, ?_⟩
    · rw [rvv_loop_shape]
      apply Exec.done (v := .integer 0)
      · simp [eval, binary, convert, loc.batch]
      · rfl
    · simpa using loc
    · simp [readBytes, widen32, sumWords]
  · let k := cfg.choose n
    have pos : 0 < k := cfg.positive n (by omega)
    have le : k ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
    have cap : k ≤ cfg.capacity := Nat.le_trans (cfg.bounded n) (Nat.min_le_right ..)
    let xs := readBytes s.memory input k
    let nextAcc := addPrefix acc (widen32 kind xs)
    let next := rvvBodyAfter kind s n k input acc xs
    have hx : xs.length = k := readBytes_length ..
    have hwide : (widen32 kind xs).length = k := by simp [widen32, hx]
    have nextLen : nextAcc.length = cfg.capacity := by
      dsimp only [nextAcc]
      rw [addPrefix_length _ _ (by rw [hwide, ha]; exact cap), ha]
    have load : loadBytes s.memory input k = some xs :=
      loadBytes_success _ _ _ (fun a h => readable a (footprint_mono le h))
    have body : Exec cfg (rvvBody kind) s next :=
      rvv_body_exec cfg kind s n input output acc xs loc bound ha hx load
    have memory : next.memory = s.memory := rvvBodyAfter_memory ..
    have nextLoc : RvvLocals next (n-k) (input + BitVec.ofNat 64 k) output cfg.capacity nextAcc :=
      rvvBodyAfter_locals kind s n k input output cfg.capacity acc xs loc
    have nextRead : ∀ a, Footprint (input + BitVec.ofNat 64 k) (n-k) a → next.memory.readable a = true := by
      intro a h
      rw [memory]
      exact readable a (footprint_shift_within (by omega) h)
    obtain ⟨t, final, execution, memFinal, finalLoc, finalLen, total⟩ :=
      rvv_loop_total cfg kind next (n-k) (input + BitVec.ofNat 64 k) output nextAcc
        nextLoc (by omega) nextLen nextRead
    refine ⟨t, final, ?_, memFinal.trans memory, ?_, finalLen, ?_⟩
    · rw [rvv_loop_shape] at execution ⊢
      apply Exec.more (v := .integer 1) (t := next)
      · simp [eval, binary, convert, loc.batch, zero, show (0 : Int) < n by omega]
      · rfl
      · exact body
      · exact execution
    · have address : input + BitVec.ofNat 64 k + BitVec.ofNat 64 (n-k) = input + BitVec.ofNat 64 n := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le le]
      rw [address] at finalLoc
      exact finalLoc
    · rw [total, memory]
      have joined := readBytes_add s.memory input k (n-k)
      rw [Nat.add_sub_of_le le] at joined
      rw [joined]
      simp only [widen32, List.map_append, sumWords_append]
      dsimp only [nextAcc]
      rw [addPrefix_sum _ _ (by rw [hwide, ha]; exact cap)]
      exact BitVec.add_assoc _ _ _
termination_by n

end Salty.Kernels.Rsum
