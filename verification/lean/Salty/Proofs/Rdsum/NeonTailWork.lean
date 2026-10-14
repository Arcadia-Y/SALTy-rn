import Salty.Proofs.Rdsum.NeonTailOutput

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

def neonTailWork (kind : Interpretation) : Stmt := takeStatements 12 (neonChannels kind false)
def tailValues (kind : Interpretation) (m : Memory) (input : Address) (stride rows : Nat) : List (BitVec 32) :=
  (List.range 8).map (columnSum kind m input stride rows)

@[simp] theorem tailValues_length (kind : Interpretation) (m : Memory) (input : Address) (stride rows : Nat) :
    (tailValues kind m input stride rows).length = 8 := by simp [tailValues]

theorem neon_tail_work_frame (kind : Interpretation) (cfg : Config) (s t : State)
    (rows channels stride : Nat) (input zero output : Address)
    (exec : Exec cfg (neonTailWork kind) s t)
    (loc : ChannelLocals s rows channels stride input zero output) :
    ChannelLocals t rows channels stride input zero output := by
  constructor
  · exact (exec.locals_frame _ (by cases kind <;> rfl)).trans loc.rows
  · exact (exec.locals_frame _ (by cases kind <;> rfl)).trans loc.channels
  · exact (exec.locals_frame _ (by cases kind <;> rfl)).trans loc.strideLocal
  · exact (exec.locals_frame _ (by cases kind <;> rfl)).trans loc.input
  · exact (exec.locals_frame _ (by cases kind <;> rfl)).trans loc.zero
  · exact (exec.locals_frame _ (by cases kind <;> rfl)).trans loc.output
  · exact (exec.locals_frame _ (by cases kind <;> rfl)).trans loc.increment

/-- Actual initialization and complete row accumulation for one NEON tail strip. -/
theorem neon_tail_work_correct (kind : Interpretation) (cfg : Config) (s : State)
    (rows channels stride : Nat) (input zero output : Address) (bound : rows < 2^31)
    (loc : ChannelLocals s rows channels stride input zero output)
    (readable : ∀ row, row < rows → ∀ a,
      Footprint (input+BitVec.ofNat 64 (row*stride)) 8 a → s.memory.readable a = true)
    (zeroRead : ∀ a, Footprint zero 8 a → s.memory.readable a = true)
    (zeros : ∀ column, column < 8 → s.memory.data (zero+BitVec.ofNat 64 column) = 0) :
    ∃ t, Exec cfg (neonTailWork kind) s t ∧ t.memory = s.memory ∧
      ChannelLocals t rows channels stride input zero output ∧
      t.locals "vacc0_2" = some (.words32 ((tailValues kind s.memory input stride rows).take 4)) ∧
      t.locals "vacc1" = some (.words32 ((tailValues kind s.memory input stride rows).drop 4)) := by
  let u := neonTailInitialized s input stride rows
  have init : Exec cfg (neonTailInit kind) s u := neon_tail_init_exec kind cfg s input stride rows bound
    loc.input loc.strideLocal loc.rows
  have umem : u.memory = s.memory := rfl
  have uloc := neonTailInitialized_locals s input zero stride rows loc.zero loc.increment
  have unum := neonTailInitialized_num s input stride rows
  obtain ⟨t,exec,mem,low,high⟩ := neon_tail_rows_correct kind cfg u input zero stride rows 0 rows
    (fun i => input+BitVec.ofNat 64 (i*stride)) (fun _ => 0) bound (by omega) uloc unum
    (by simpa only [umem] using readable) (by simpa only [umem] using zeroRead)
    (by simpa only [umem] using zeros) (by intro i hi hr; simp)
  have work : Exec cfg (neonTailWork kind) s t := by
    apply exec_take_drop (t := u) 11
    · have shape : takeStatements 11 (neonTailWork kind) = neonTailInit kind := by cases kind <;> rfl
      rw [shape]; exact init
    · have shape : dropStatements 11 (neonTailWork kind) = .seq (neonRowLoop kind false) .skip := by cases kind <;> rfl
      rw [shape]; exact .seq exec .skip
  refine ⟨t,work,mem.trans umem,neon_tail_work_frame kind cfg s t rows channels stride input zero output work loc,?_,?_⟩
  · simpa [tailValues, umem, intervalSum_zero] using low
  · simpa [tailValues, umem, intervalSum_zero] using high

end Salty.Kernels.Rdsum
