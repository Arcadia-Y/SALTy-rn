import Salty.Proofs.Rdsum.NeonMainOutput

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

def neonMainWork (kind : Interpretation) : Stmt :=
  takeStatements (9+neonWidth kind true/4) (neonChannels kind true)

theorem neon_main_work_frame (kind : Interpretation) (cfg : Config) (s t : State)
    (rows channels stride : Nat) (input zero output : Address)
    (exec : Exec cfg (neonMainWork kind) s t)
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

theorem neon_main_work_correct (kind : Interpretation) (cfg : Config) (s : State)
    (rows channels stride : Nat) (input zero output : Address) (bound : rows < 2^31)
    (loc : ChannelLocals s rows channels stride input zero output)
    (readable : ∀ row, row < rows → ∀ a,
      Footprint (input+BitVec.ofNat 64 (row*stride)) (mainReadSpan kind) a → s.memory.readable a = true)
    (zeroRead : ∀ a, Footprint zero (mainReadSpan kind) a → s.memory.readable a = true)
    (zeros : ∀ column, column < neonWidth kind true → s.memory.data (zero+BitVec.ofNat 64 column) = 0) :
    ∃ t, Exec cfg (neonMainWork kind) s t ∧ t.memory = s.memory ∧
      ChannelLocals t rows channels stride input zero output ∧
      (∀ word, word < neonWidth kind true/4 → t.locals (neonWordName true word) =
        some (.words32 (wordValues (columnSum kind s.memory input stride rows) word))) := by
  let u := neonMainInitialized kind s input stride rows
  have init : Exec cfg (neonMainInit kind) s u := neon_main_init_exec kind cfg s input stride rows bound
    loc.input loc.strideLocal loc.rows
  have umem : u.memory = s.memory := neonMainInitialized_memory kind s input stride rows
  obtain ⟨t,loop,mem,words⟩ := neon_main_rows_correct kind cfg u input zero stride rows 0 rows
    (fun i => input+BitVec.ofNat 64 (i*stride)) (fun _ => 0) bound (by omega)
    (neonMainInitialized_locals kind s input zero stride rows loc.zero loc.increment)
    (by simpa only [umem] using readable) (by simpa only [umem] using zeroRead)
    (by simpa only [umem] using zeros) (by intro i hi hr; simp)
  have work : Exec cfg (neonMainWork kind) s t := by
    apply exec_take_drop (t := u) (8+neonWidth kind true/4)
    · have shape : takeStatements (8+neonWidth kind true/4) (neonMainWork kind) = neonMainInit kind := by cases kind <;> rfl
      rw [shape]; exact init
    · have shape : dropStatements (8+neonWidth kind true/4) (neonMainWork kind) = .seq (neonRowLoop kind true) .skip := by cases kind <;> rfl
      rw [shape]; exact .seq loop .skip
  refine ⟨t,work,mem.trans umem,neon_main_work_frame kind cfg s t rows channels stride input zero output work loc,?_⟩
  intro word hw
  simpa [umem, intervalSum_zero] using words word hw

end Salty.Kernels.Rdsum
