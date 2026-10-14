import Salty.Proofs.Rdsum.NeonTailLoop

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def neonTail (kind : Interpretation) : Stmt := firstStatement (dropStatements 6 (neonProgram kind))
def tailHeaderCount : Interpretation → Nat
  | .signed => 1
  | .unsigned => 2

def neonTailHeader (kind : Interpretation) : Stmt :=
  takeStatements (tailHeaderCount kind) (branchYes (neonTail kind))

def tailIncrement : Stmt := .assign "input_increment"
  (.cast .u64 (.bin .mul (.cast .u64 (.lit 7)) (.var "input_stride")))

def tailAssertion : Stmt := .effect .assertion
  [.not (.not (.conditional (.bin .ge (.var "channels") (.cast .u64 (.lit 1)))
    (.conditional (.bin .le (.var "channels") (.cast .u64 (.lit 31))) (.lit 1) (.lit 0)) (.lit 0)))]

theorem neon_tail_header_shape (kind : Interpretation) : neonTailHeader kind =
    match kind with
    | .signed => .seq tailIncrement .skip
    | .unsigned => .seq tailAssertion (.seq tailIncrement .skip) := by cases kind <;> rfl

theorem neon_tail_header_exec (kind : Interpretation) (cfg : Config) (s : State) (channels stride : Nat)
    (positive : 0 < channels) (small : channels < neonWidth kind true) (bound : 7*stride < 2^64)
    (hc : s.locals "channels" = some (.integer channels))
    (hs : s.locals "input_stride" = some (.integer stride)) :
    Exec cfg (neonTailHeader kind) s (update s "input_increment" (.integer (7*stride))) := by
  have cast : convert .u64 (7*(stride : Int)) = (7*stride : Nat) := by simpa using cast_nat (7*stride) bound
  rw [neon_tail_header_shape]
  cases kind with
  | signed =>
    apply run_sound (fuel := 4)
    simp [tailIncrement, run, eval, binary, hs, cast, show convert .u64 7 = 7 from rfl]
  | unsigned =>
    have c1 : (1 : Int) ≤ channels := by omega
    have c31 : (channels : Int) ≤ 31 := by simp only [neonWidth, ↓reduceIte] at small; omega
    apply run_sound (fuel := 5)
    simp [tailAssertion, tailIncrement, run, eval, binary, effect, truth, hs, hc, cast, c1, c31,
      show convert .u64 1 = 1 from rfl, show convert .u64 7 = 7 from rfl, show convert .u64 31 = 31 from rfl]

theorem neon_tail_shape (kind : Interpretation) : neonTail kind =
    .branch (.bin .ne (.var "channels") (.cast .u64 (.lit 0))) (branchYes (neonTail kind)) .skip := by
  cases kind <;> rfl

/-- Complete guarded NEON tail, including the unsigned source assertion and
its do/while entry, against the original-memory scalar output specification. -/
theorem neon_tail_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero output : Address) (rows stride channels : Nat)
    (rowBound : rows < 2^31) (strideBound : 7*stride < 2^64)
    (small : channels < neonWidth kind true)
    (loc : ChannelLocals s rows channels stride input zero output)
    (safe : NeonSafe kind s.memory input zero output rows stride channels) :
    ∃ t, Exec cfg (neonTail kind) s t ∧
      t.memory = writeBytes s.memory output (encodeWords32 (stripWords kind s.memory input output rows stride channels)) ∧
      t.locals "channels" = some (.integer 0) := by
  by_cases empty : channels = 0
  · subst channels
    refine ⟨s,?_,rfl,loc.channels⟩
    rw [neon_tail_shape]
    apply Exec.no (v := .integer 0)
    · simp [eval, binary, loc.channels, show convert .u64 0 = 0 from rfl]
    · rfl
    · exact .skip
  · have positive : 0 < channels := by omega
    have channelBound : channels < 2^64 := by cases kind <;> simp only [neonWidth, ↓reduceIte] at small <;> omega
    let u := update s "input_increment" (.integer (7*stride))
    have header : Exec cfg (neonTailHeader kind) s u := neon_tail_header_exec kind cfg s channels stride positive small strideBound loc.channels loc.strideLocal
    have uloc : ChannelLocals u rows channels stride input zero output := by
      constructor <;> simp [u, update, loc.rows, loc.channels, loc.strideLocal, loc.input, loc.zero, loc.output]
    obtain ⟨t,body,mem,done⟩ := neon_tail_do_correct kind cfg u input zero output rows stride channels positive rowBound channelBound uloc safe
    refine ⟨t,?_,mem,done⟩
    rw [neon_tail_shape]
    apply Exec.yes (v := .integer 1)
    · simp [eval, binary, loc.channels, empty, show convert .u64 0 = 0 from rfl]
    · rfl
    · apply exec_take_drop (t := u) (tailHeaderCount kind) header
      have shape : dropStatements (tailHeaderCount kind) (branchYes (neonTail kind)) =
          .seq (neonTailDo kind) .skip := by cases kind <;> rfl
      rw [shape]
      exact .seq body .skip

end Salty.Kernels.Rdsum
