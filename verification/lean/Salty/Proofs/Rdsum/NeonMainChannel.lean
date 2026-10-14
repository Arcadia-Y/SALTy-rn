import Salty.Proofs.Rdsum.NeonMainAdvance
import Salty.Proofs.Rdsum.NeonTail

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

/-- One complete main channel strip, including every source load, sum, store,
and input/channel advance. -/
theorem neon_main_channel_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero output : Address) (rows stride channels : Nat)
    (rowBound : rows < 2^31) (channelBound : channels < 2^64)
    (within : neonWidth kind true ≤ channels)
    (loc : ChannelLocals s rows channels stride input zero output)
    (safe : NeonSafe kind s.memory input zero output rows stride channels) :
    ∃ t, Exec cfg (neonMainChannelIteration kind) s t ∧
      t.memory = writeBytes s.memory output (encodeWords32 (stripWords kind s.memory input output rows stride (neonWidth kind true))) ∧
      ChannelLocals t rows (channels-neonWidth kind true) stride
        (input+BitVec.ofNat 64 (neonWidth kind true)) zero (output+BitVec.ofNat 64 (4*neonWidth kind true)) := by
  have span : mainReadSpan kind ≤ channels+15 := by cases kind <;> simp [neonWidth,mainReadSpan] at within ⊢ <;> omega
  have zeroSpan : mainReadSpan kind ≤ 40 := by cases kind <;> decide
  have width40 : neonWidth kind true ≤ 40 := by cases kind <;> decide
  obtain ⟨u,work,umem,uloc,words⟩ := neon_main_work_correct kind cfg s rows channels stride input zero output rowBound loc
    (fun row hr a ha => safe.inputPadRead row hr a (footprint_mono span ha))
    (fun a ha => safe.zeroPadRead a (footprint_mono zeroSpan ha))
    (fun column hc => safe.zeroPadContents _ ⟨column,by omega,rfl⟩)
  obtain ⟨v,store,vmem,vout⟩ := neon_main_output_correct kind cfg u output (columnSum kind s.memory input stride rows)
    uloc.output words
    (fun a ha => by rw [umem]; exact safe.outRead a (footprint_mono (by omega) ha))
    (fun a ha => by rw [umem]; exact safe.outWrite a (footprint_mono (by omega) ha))
  have vi : v.locals "input" = some (.pointer input) :=
    (store.locals_frame "input" (by cases kind <;> rfl)).trans uloc.input
  let w := update v "input" (.pointer (input+BitVec.ofNat 64 (neonWidth kind true)))
  have advance : Exec cfg (neonMainAdvance kind) v w := neon_main_advance_exec kind cfg v input vi
  have body : Exec cfg (neonChannels kind true) s w := by
    apply exec_take_drop (t := u) (9+neonWidth kind true/4) work
    apply exec_take_drop (t := v) (1+5*(neonWidth kind true/4)) store
    have shape : dropStatements (1+5*(neonWidth kind true/4))
        (dropStatements (9+neonWidth kind true/4) (neonChannels kind true)) = neonMainAdvance kind := by cases kind <;> rfl
    rw [shape]; exact advance
  have wloc : ChannelLocals w rows channels stride
      (input+BitVec.ofNat 64 (neonWidth kind true)) zero (output+BitVec.ofNat 64 (4*neonWidth kind true)) := by
    constructor
    · exact (body.locals_frame _ (by cases kind <;> rfl)).trans loc.rows
    · exact (body.locals_frame _ (by cases kind <;> rfl)).trans loc.channels
    · exact (body.locals_frame _ (by cases kind <;> rfl)).trans loc.strideLocal
    · simp [w,update]
    · exact (body.locals_frame _ (by cases kind <;> rfl)).trans loc.zero
    · simpa [w,update] using vout
    · exact (body.locals_frame _ (by cases kind <;> rfl)).trans loc.increment
  let t := update w "channels" (.integer (channels-neonWidth kind true : Nat))
  have sub := neon_main_subtract_exec kind cfg w channels channelBound within wloc.channels
  refine ⟨t,?_,?_,?_⟩
  · have shape : neonMainChannelIteration kind = .seq (neonChannels kind true) (neonMainSubtract kind) := by cases kind <;> rfl
    rw [shape]; exact .seq body sub
  · change v.memory = _
    simpa only [umem,stripWords] using vmem
  · constructor
    · simpa [t,update] using wloc.rows
    · simp [t,update]
    · simpa [t,update] using wloc.strideLocal
    · simpa [t,update] using wloc.input
    · simpa [t,update] using wloc.zero
    · simpa [t,update] using wloc.output
    · simpa [t,update] using wloc.increment

end Salty.Kernels.Rdsum
