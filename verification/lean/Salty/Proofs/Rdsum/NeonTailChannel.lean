import Salty.Proofs.Rdsum.NeonTailWork

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

theorem stored_tail_values (kind : Interpretation) (m : Memory) (input output : Address)
    (rows stride width : Nat) (within : width ≤ 8) :
    storedWords m output width ((tailValues kind m input stride rows).take width) =
      stripWords kind m input output rows stride width := by
  simp only [tailValues, ← List.map_take, List.take_range, Nat.min_eq_left within]
  exact storedWords_columns m output width (columnSum kind m input stride rows)

/-- One complete extracted NEON tail iteration, for every row count in the
contract. The final short strip retains the source's unadvanced odd pointer. -/
theorem neon_tail_channel_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero output : Address) (rows stride channels : Nat)
    (rowBound : rows < 2^31) (channelBound : channels < 2^64)
    (loc : ChannelLocals s rows channels stride input zero output)
    (readable : ∀ row, row < rows → ∀ a,
      Footprint (input+BitVec.ofNat 64 (row*stride)) 8 a → s.memory.readable a = true)
    (zeroRead : ∀ a, Footprint zero 8 a → s.memory.readable a = true)
    (zeros : ∀ column, column < 8 → s.memory.data (zero+BitVec.ofNat 64 column) = 0)
    (outRead : ∀ a, Footprint output (4*min channels 8) a → s.memory.readable a = true)
    (outWrite : ∀ a, Footprint output (4*min channels 8) a → s.memory.writable a = true)
    (defined : channels < 8 → LastOriginalDefined kind s.memory output (tailValues kind s.memory input stride rows) channels) :
    ∃ t, Exec cfg (neonChannels kind false) s t ∧
      t.memory = writeBytes s.memory output
        (encodeWords32 (stripWords kind s.memory input output rows stride (min channels 8))) ∧
      (if 8 ≤ channels then ChannelLocals t rows (channels-8) stride (input+8) zero (output+32)
       else t.locals "channels" = some (.integer 0)) := by
  obtain ⟨u,work,mem,uloc,low,high⟩ := neon_tail_work_correct kind cfg s rows channels stride input zero output rowBound loc readable zeroRead zeros
  let values := tailValues kind s.memory input stride rows
  have ll : (values.take 4).length = 4 := by simp [values]
  have hl : (values.drop 4).length = 4 := by simp [values]
  have concat : values.take 4++values.drop 4 = values := List.take_append_drop ..
  let t := tailOutputAfter u input output (values.take 4) (values.drop 4) channels
  have store : Exec cfg (neonTailOutput kind) u t := neon_tail_output_exec kind cfg u input output
    (values.take 4) (values.drop 4) ll hl channels channelBound uloc.channels uloc.input uloc.output low high
    (by simpa only [mem] using outRead) (by simpa only [mem] using outWrite)
    (by simpa only [mem, concat] using defined)
  refine ⟨t,?_,?_,tailOutputAfter_locals u input zero output (values.take 4) (values.drop 4) rows channels stride uloc⟩
  · apply exec_take_drop (t := u) 12 work
    have shape : dropStatements 12 (neonChannels kind false) = .seq (neonTailOutput kind) .skip := by cases kind <;> rfl
    rw [shape]
    exact .seq store .skip
  · rw [tailOutputAfter_memory u input output (values.take 4) (values.drop 4) ll hl channels,
      mem, concat, stored_tail_values kind s.memory input output rows stride (min channels 8) (Nat.min_le_right ..)]

end Salty.Kernels.Rdsum
