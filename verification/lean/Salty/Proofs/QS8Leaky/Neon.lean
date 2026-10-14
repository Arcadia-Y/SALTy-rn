import Salty.Proofs.QS8Leaky.Tail
import Salty.Proofs.S8Clamp.Neon

namespace Salty.Kernels.QS8Leaky
open CByte
open S8Clamp.Execution (PaddedSafe)

def neon8AndTail : Stmt := dropStatements 8 Generated.QS8Leaky.neon

theorem neon8AndTail_shape : neon8AndTail = .seq neon8Loop (.seq neonTail .skip) := rfl

theorem neon8After_locals (s : State) (n : Nat) (input output : Address) (p : Params)
    (bs : List Byte) (m : Memory) (h : NeonLocals s n input output p) :
    NeonLocals (neon8After s n input output p bs m) (n - 8) (input + 8) (output + 8) p := by
  constructor <;> simp [neon8After, update, h.inputZero, h.positive, h.negative, h.outputZero]

/-- Complete extracted 8-byte loop followed by the extracted padded tail. -/
theorem neon8_tail_total (cfg : Config) (s : State) (n : Nat) (input output : Address)
    (p : Params) (locals : NeonLocals s n input output p)
    (bound : n < 2^64) (safe : PaddedSafe s.memory input output n) :
    ∃ t, Exec cfg neon8AndTail s t ∧
      t.memory = writeBytes s.memory output ((readBytes s.memory input n).map (neonLane p)) := by
  by_cases small : n < 8
  · obtain ⟨t, htail, hm⟩ := neon_tail_total cfg s n input output p locals small
      (fun hn a ha => safe.readable a (footprint_mono (by omega) ha)) safe.writable
    refine ⟨t, ?_, hm⟩
    rw [neon8AndTail_shape]
    apply Exec.seq (t := s)
    · apply Exec.done (v := .integer 0)
      · simp [neon8Loop, firstStatement, dropStatements, Generated.QS8Leaky.neon,
          eval, binary, convert, Int.max_def, locals.batch, show ¬ (8 : Int) ≤ n by omega]
      · rfl
    · exact .seq htail .skip
  · have large : 8 ≤ n := by omega
    let bs := readBytes s.memory input 8
    let written := bs.map (neonLane p)
    let m := writeBytes s.memory output written
    let next := neon8After s n input output p bs m
    have len : written.length = 8 := by simp [written, bs]
    have load : loadBytes s.memory input 8 = some bs :=
      loadBytes_success _ _ _ (fun a ha => safe.readable a (footprint_mono (by omega) ha))
    have store : storeBytes s.memory output written = some m :=
      storeBytes_success _ _ _ (fun a ha => safe.writable a (footprint_mono (by omega) ha))
    have body : Exec cfg neon8Body s next := neon8_body_exec cfg s n input output p bs m
      locals bound large (readBytes_length ..) load store
    have nextlocals := neon8After_locals s n input output p bs m locals
    have nextsafe : PaddedSafe next.memory (input + 8) (output + 8) (n - 8) := by
      simpa using safe.advance large written len
    obtain ⟨t, hrun, hm⟩ := neon8_tail_total cfg next (n - 8) (input + 8) (output + 8)
      p nextlocals (by omega) nextsafe
    refine ⟨t, ?_, ?_⟩
    · rw [neon8AndTail_shape] at hrun ⊢
      cases hrun with
      | seq hloop htail =>
        apply Exec.seq (Exec.more (v := .integer 1) ?_ rfl body hloop) htail
        simp [neon8Loop, firstStatement, dropStatements, Generated.QS8Leaky.neon,
          eval, binary, convert, Int.max_def, locals.batch, show (8 : Int) ≤ n by omega]
    · rw [hm]
      change writeBytes m (output + 8)
        ((readBytes m (input + 8) (n - 8)).map (neonLane p)) = _
      have remaining := safe.region.remaining_read large written len
      have remaining' : readBytes m (input + 8) (n - 8) = readBytes s.memory (input + 8) (n - 8) := by
        simpa using remaining
      rw [remaining']
      have split : n = 8 + (n - 8) := by omega
      conv => rhs; rw [split, readBytes_add, List.map_append, writeBytes_append]
      simp only [List.length_map, readBytes_length]
      rfl
termination_by n

end Salty.Kernels.QS8Leaky
