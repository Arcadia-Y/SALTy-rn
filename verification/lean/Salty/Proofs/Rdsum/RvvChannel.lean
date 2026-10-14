import Salty.Proofs.Rdsum.RvvAdvance

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 2000000

def stripWords (kind : Interpretation) (m : Memory) (input output : Address)
    (rows stride width : Nat) : List (BitVec 32) :=
  (List.range width).map (fun column => readWord32 m (output+BitVec.ofNat 64 (4*column)) +
    columnSum kind m input stride rows column)

/-- One complete extracted scalable channel iteration. All row batches execute
before the old output words are loaded, added, and stored. -/
theorem rvv_channel_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero output : Address) (rows stride channels : Nat)
    (rowBound : rows < 2^31) (channelBound : channels < 2^64)
    (loc : ChannelLocals s rows channels stride input zero output)
    (readable : ∀ row, row < rows → ∀ a,
      Footprint (input+BitVec.ofNat 64 (row*stride)) (cfg.choose channels) a → s.memory.readable a = true)
    (zeroRead : ∀ a, Footprint zero (cfg.choose channels) a → s.memory.readable a = true)
    (zeros : ∀ column, column < cfg.choose channels → s.memory.data (zero+BitVec.ofNat 64 column) = 0)
    (outRead : ∀ a, Footprint output (4*cfg.choose channels) a → s.memory.readable a = true)
    (outWrite : ∀ a, Footprint output (4*cfg.choose channels) a → s.memory.writable a = true) :
    ∃ t, Exec cfg (rvvChannels kind) s t ∧
      t.memory = writeBytes s.memory output (encodeWords32 (stripWords kind s.memory input output rows stride (cfg.choose channels))) ∧
      ChannelLocals t rows (channels-cfg.choose channels) stride
        (input+BitVec.ofNat 64 (cfg.choose channels)) zero (output+BitVec.ofNat 64 (4*cfg.choose channels)) := by
  let width := cfg.choose channels
  have cap : width ≤ cfg.capacity := Nat.le_trans (cfg.bounded channels) (Nat.min_le_right ..)
  have within : width ≤ channels := Nat.le_trans (cfg.bounded channels) (Nat.min_le_left ..)
  let u := channelInitialized kind s input stride rows width
  have init : Exec cfg (rvvChannelInit kind) s u := rvv_channel_init_exec kind cfg s input stride rows channels
    rowBound loc.channels loc.input loc.strideLocal loc.rows
  have umem : u.memory = s.memory := channelInitialized_memory kind s input stride rows width
  obtain ⟨v,loop,mem,acc⟩ := rvv_rows_correct kind cfg u input zero width stride rows 0 rows
    (fun i => input+BitVec.ofNat 64 (i*stride)) (fun _ => 0) rowBound (by omega) cap
    (channelInitialized_locals kind s input zero stride rows width loc.zero loc.increment)
    (by simpa only [umem] using readable) (by simpa only [umem] using zeroRead)
    (by simpa only [umem] using zeros) (by intro i hi live; simp)
  have vmem : v.memory = s.memory := mem.trans umem
  have av : v.locals (accumulatorName kind) = some (.words32 ((List.range width).map
      (fun column => columnSum kind s.memory input stride rows column))) := by
    simpa [umem, intervalSum_zero] using acc
  have vout : v.locals "output" = some (.pointer output) :=
    ((loop.locals_frame "output" (by cases kind <;> rfl)).trans
      (init.locals_frame "output" (by cases kind <;> rfl))).trans loc.output
  have vvl : v.locals "vl" = some (.integer width) :=
    (loop.locals_frame "vl" (by cases kind <;> rfl)).trans
      (channelInitialized_locals kind s input zero stride rows width loc.zero loc.increment).vl
  let values := (List.range width).map (fun column => columnSum kind s.memory input stride rows column)
  let w := storeAfter v output width values
  have store : Exec cfg (rvvStore kind) v w := rvv_store_exec kind cfg v output width values (by simp [values]) cap
    vout vvl av (by simpa only [vmem] using outRead) (by simpa only [vmem] using outWrite)
  have work : Exec cfg (takeStatements 14 (rvvChannels kind)) s w := by
    apply exec_take_drop (t := u) 10
    · have shape : takeStatements 10 (takeStatements 14 (rvvChannels kind)) = rvvChannelInit kind := by cases kind <;> rfl
      rw [shape]
      exact init
    · have shape : dropStatements 10 (takeStatements 14 (rvvChannels kind)) =
          .seq (rvvRowLoop kind) (rvvStore kind) := by cases kind <;> rfl
      rw [shape]
      exact .seq loop store
  have wloc : ChannelLocals w rows channels stride input zero output := by
    constructor
    · exact (work.locals_frame "rows" (by cases kind <;> rfl)).trans loc.rows
    · exact (work.locals_frame "channels" (by cases kind <;> rfl)).trans loc.channels
    · exact (work.locals_frame "input_stride" (by cases kind <;> rfl)).trans loc.strideLocal
    · exact (work.locals_frame "input" (by cases kind <;> rfl)).trans loc.input
    · exact (work.locals_frame "zero" (by cases kind <;> rfl)).trans loc.zero
    · exact (work.locals_frame "output" (by cases kind <;> rfl)).trans loc.output
    · exact (work.locals_frame "input_increment" (by cases kind <;> rfl)).trans loc.increment
  have wvl : w.locals "vl" = some (.integer width) := (store.locals_frame "vl" (by cases kind <;> rfl)).trans vvl
  let t := channelAdvanced kind w input output channels width
  have advance : Exec cfg (rvvAdvance kind) w t := rvv_advance_exec kind cfg w input output channels width
    channelBound within wloc.input wloc.output wloc.channels wvl
  refine ⟨t,exec_take_drop 14 work advance,?_,channelAdvanced_locals kind w rows channels stride width input zero output wloc⟩
  rw [channelAdvanced_memory]
  change writeBytes v.memory output (encodeWords32 (storedWords v.memory output width values)) = _
  rw [vmem, storedWords_columns]
  rfl

end Salty.Kernels.Rdsum
