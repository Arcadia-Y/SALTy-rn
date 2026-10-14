import Salty.Proofs.Core.CReduction
import Salty.Proofs.Core.CByteSyntax
import Salty.Proofs.Core.CByteMemory
import Salty.Generated.QS8RsumNeon
import Salty.Generated.QU8RsumNeon

namespace Salty.Kernels.Rsum
open CByte ReductionISA

def neonProgram : Interpretation → Stmt
  | .signed => Generated.QS8Rsum.neon
  | .unsigned => Generated.QU8Rsum.neon

def neonOuter (kind : Interpretation) : Stmt := firstStatement (dropStatements 6 (neonProgram kind))
def neonOuterBody (kind : Interpretation) : Stmt := loopBody (neonOuter kind)
def neonOuterCompound (kind : Interpretation) : Stmt := firstStatement (neonOuterBody kind)
def neonPartial (kind : Interpretation) : Stmt := firstStatement (dropStatements 7 (neonProgram kind))
def branchYes : Stmt → Stmt
  | .branch _ yes _ => yes
  | _ => .skip

def neonPartialBody (kind : Interpretation) : Stmt := branchYes (neonPartial kind)

inductive Stage where
  | full | remainder
  deriving DecidableEq, Repr

def countName : Stage → String | .full => "current_batch" | .remainder => "batch"
def accumulatorName : Stage → String | .full => "vacc16_0" | .remainder => "vacc16"
def loadedName : Stage → String | .full => "vt0" | .remainder => "vt"

def neonBlockLoop (kind : Interpretation) : Stage → Stmt
  | .full => dropStatements 1 (firstStatement (dropStatements 1 (neonOuterCompound kind)))
  | .remainder => firstStatement (dropStatements 2 (neonPartialBody kind))

def neonBlockBody (kind : Interpretation) (stage : Stage) : Stmt := loopBody (neonBlockLoop kind stage)

def blockCond (stage : Stage) : Expr :=
  .bin (match stage with | .full => .gt | .remainder => .ge)
    (.var (countName stage)) (.cast .u64 (.lit (match stage with | .full => 0 | .remainder => 16)))

theorem block_loop_shape (kind : Interpretation) (stage : Stage) :
    neonBlockLoop kind stage = .loop (blockCond stage) (neonBlockBody kind stage) := by
  cases kind <;> cases stage <;> rfl

structure BlockLocals (stage : Stage) (s : State) (n : Nat) (input : Address) (acc : List (BitVec 16)) : Prop where
  count : s.locals (countName stage) = some (.integer n)
  inputPtr : s.locals "input" = some (.pointer input)
  accumulator : s.locals (accumulatorName stage) = some (.halfwords acc)

def neonBlockAfter (kind : Interpretation) (stage : Stage) (s : State) (n : Nat)
    (input : Address) (acc : List (BitVec 16)) (xs : List Byte) : State :=
  let t := update s (loadedName stage) (.vector 1 xs)
  let t := update t "input" (.pointer (input + 16))
  let t := update t (accumulatorName stage) (.halfwords (pairAcc16 kind acc xs))
  update t (countName stage) (.integer (n-16 : Nat))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem neon_block_body_exec (cfg : Config) (kind : Interpretation) (stage : Stage) (s : State)
    (n : Nat) (input : Address) (acc : List (BitVec 16)) (xs : List Byte)
    (loc : BlockLocals stage s n input acc) (bound : n < 2^64) (enough : 16 ≤ n)
    (ha : acc.length = 8) (hx : xs.length = 16) (load : loadBytes s.memory input 16 = some xs) :
    Exec cfg (neonBlockBody kind stage) s (neonBlockAfter kind stage s n input acc xs) := by
  have sub : max (((n : Int) - 16) % 18446744073709551616) 0 = (n-16 : Nat) := by
    simpa [convert] using cast_sub n 16 enough bound
  have count := loc.count
  have accumulator := loc.accumulator
  cases kind <;> cases stage <;>
    simp only [countName, accumulatorName] at count accumulator <;>
    apply run_sound (fuel := 16) <;>
    simp +contextual [neonBlockBody, neonBlockLoop, neonOuterCompound, neonOuterBody, neonOuter,
      neonPartialBody, neonPartial, branchYes, neonProgram, Generated.QS8Rsum.neon, Generated.QU8Rsum.neon,
      firstStatement, dropStatements, loopBody, run, eval, intrinsic, reductionIntrinsic, binary,
      convert, count, loc.inputPtr, accumulator, neonBlockAfter, loadedName,
      countName, accumulatorName, update, load, ha, hx, show max (16 : Int) 0 = 16 by decide, sub]

theorem neonBlockAfter_memory (kind : Interpretation) (stage : Stage) (s : State) (n : Nat)
    (input : Address) (acc : List (BitVec 16)) (xs : List Byte) :
    (neonBlockAfter kind stage s n input acc xs).memory = s.memory := rfl

theorem neonBlockAfter_locals (kind : Interpretation) (stage : Stage) (s : State) (n : Nat)
    (input : Address) (acc : List (BitVec 16)) (xs : List Byte) :
    BlockLocals stage (neonBlockAfter kind stage s n input acc xs) (n-16) (input+16) (pairAcc16 kind acc xs) := by
  cases stage <;> constructor <;> simp [neonBlockAfter, update, countName, accumulatorName, loadedName]

theorem block_cond_done (cfg : Config) (stage : Stage) (s : State) (r : Nat) (input : Address)
    (acc : List (BitVec 16)) (loc : BlockLocals stage s r input acc)
    (hr : r < 16) (full : stage = .full → r = 0) : eval cfg s (blockCond stage) = some (.integer 0) := by
  have count := loc.count
  cases stage with
  | full =>
    have zero := full rfl
    subst r
    simp only [countName] at count
    simp [blockCond, countName, eval, binary, convert, count]
  | remainder =>
    simp only [countName] at count
    simp [blockCond, countName, eval, binary, convert, Int.max_def, count, show ¬ (16 : Int) ≤ r by omega]

theorem block_cond_more (cfg : Config) (stage : Stage) (s : State) (n : Nat) (input : Address)
    (acc : List (BitVec 16)) (loc : BlockLocals stage s n input acc) (hn : 16 ≤ n) :
    eval cfg s (blockCond stage) = some (.integer 1) := by
  have count := loc.count
  have nonzero : n ≠ 0 := by omega
  cases stage <;> simp only [countName] at count <;>
    simp [blockCond, countName, eval, binary, convert, Int.max_def, count, nonzero, show (16 : Int) ≤ n by omega]

/-- The actual full-block and remainder16byte loops, with an accumulator range
invariant. At most128 pair updates occur before widening to32bits. -/
theorem neon_block_loop_total (cfg : Config) (kind : Interpretation) (stage : Stage)
    (q r k : Nat) (s : State) (input : Address) (acc : List (BitVec 16))
    (loc : BlockLocals stage s (16*q+r) input acc)
    (hr : r < 16) (full : stage = .full → r = 0) (size : 16*q+r < 2^64)
    (length : acc.length = 8) (bounds : ∀ a ∈ acc, LaneBound kind k a)
    (limit : k + q ≤ 128)
    (readable : ∀ a, Footprint input (16*q) a → s.memory.readable a = true) :
    ∃ t final, Exec cfg (neonBlockLoop kind stage) s t ∧ t.memory = s.memory ∧
      BlockLocals stage t r (input + BitVec.ofNat 64 (16*q)) final ∧
      final.length = 8 ∧ (∀ a ∈ final, LaneBound kind (k+q) a) ∧
      sumWords (widen32 kind final) = sumWords (widen32 kind acc) +
        sumWords (widen32 kind (readBytes s.memory input (16*q))) := by
  induction q generalizing k s input acc with
  | zero =>
    refine ⟨s, acc, ?_, rfl, ?_, length, ?_, ?_⟩
    · rw [block_loop_shape]
      apply Exec.done (v := .integer 0)
      · exact block_cond_done cfg stage s r input acc (by simpa using loc) hr full
      · rfl
    · simpa using loc
    · simpa using bounds
    · simp [readBytes, widen32, sumWords]
  | succ q ih =>
    let xs := readBytes s.memory input 16
    let nextAcc := pairAcc16 kind acc xs
    let next := neonBlockAfter kind stage s (16*(q+1)+r) input acc xs
    have hx : xs.length = 16 := readBytes_length ..
    have pairLen : xs.length = 2*acc.length := by rw [hx, length]
    have hk : k < 128 := by omega
    have nextLength : nextAcc.length = 8 := (pairAcc16_length kind acc xs pairLen).trans length
    have nextBounds : ∀ a ∈ nextAcc, LaneBound kind (k+1) a := pairAcc16_bounds kind k hk acc xs bounds
    have load : loadBytes s.memory input 16 = some xs :=
      loadBytes_success _ _ _ (fun a ha => readable a (footprint_mono (by omega) ha))
    have body : Exec cfg (neonBlockBody kind stage) s next :=
      neon_block_body_exec cfg kind stage s (16*(q+1)+r) input acc xs loc size (by omega) length hx load
    have memory : next.memory = s.memory := rfl
    have nextLoc : BlockLocals stage next (16*q+r) (input+16) nextAcc := by
      have h := neonBlockAfter_locals kind stage s (16*(q+1)+r) input acc xs
      have eq : 16*(q+1)+r-16 = 16*q+r := by omega
      rw [eq] at h
      exact h
    have nextRead : ∀ a, Footprint (input+16) (16*q) a → next.memory.readable a = true := by
      intro a ha
      exact readable a (footprint_shift_within (start := 16) (by omega) ha)
    obtain ⟨t, final, execution, memFinal, finalLoc, finalLength, finalBounds, total⟩ :=
      ih (k+1) next (input+16) nextAcc nextLoc (by omega) nextLength nextBounds (by omega) nextRead
    refine ⟨t, final, ?_, memFinal.trans memory, ?_, finalLength, ?_, ?_⟩
    · rw [block_loop_shape] at execution ⊢
      apply Exec.more (v := .integer 1) (t := next)
      · exact block_cond_more cfg stage s _ input acc loc (by omega)
      · rfl
      · exact body
      · exact execution
    · have address : input + 16 + BitVec.ofNat 64 (16*q) = input + BitVec.ofNat 64 (16*(q+1)) := by
        change input + BitVec.ofNat 64 16 + BitVec.ofNat 64 (16*q) = _
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        congr 2
        omega
      rw [address] at finalLoc
      exact finalLoc
    · have counts : k+1+q = k+(q+1) := by omega
      rw [counts] at finalBounds
      exact finalBounds
    · rw [total, memory]
      have joined := readBytes_add s.memory input 16 (16*q)
      have count : 16+16*q = 16*(q+1) := by omega
      rw [count] at joined
      rw [joined]
      dsimp only [nextAcc]
      rw [pairAcc16_sum kind k hk acc xs pairLen bounds]
      simp only [widen32, List.map_append, sumWords_append, BitVec.add_assoc]
      rfl

end Salty.Kernels.Rsum
