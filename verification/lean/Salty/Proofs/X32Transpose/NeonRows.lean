import Salty.Proofs.X32Transpose.Execution

namespace Salty.Kernels.X32Transpose
open CByte

/-- Actual padded two-word source loads and two-word column stores, for every
remaining pair of rows. Output columns may alias on the final narrow tile. -/
structure NeonPairsSafe (m : Memory) (i0 i1 o0 o1 : Address) (offset pairs : Nat) : Prop where
  readable0 : ∀ r, r < pairs → ∀ p, Footprint (rowAddress i0 offset r) 8 p → m.readable p = true
  readable1 : ∀ r, r < pairs → ∀ p, Footprint (rowAddress i1 offset r) 8 p → m.readable p = true
  writable0 : ∀ r, r < pairs → ∀ p, Footprint (rowAddress o0 8 r) 8 p → m.writable p = true
  writable1 : ∀ r, r < pairs → ∀ p, Footprint (rowAddress o1 8 r) 8 p → m.writable p = true

def neonPairMemory (m : Memory) (i0 i1 o0 o1 : Address) : Memory :=
  let a := readBytes m i0 4
  let b := readBytes m (i0 + 4#64) 4
  let c := readBytes m i1 4
  let d := readBytes m (i1 + 4#64) 4
  writeBytes (writeBytes m o1 (b ++ d)) o0 (a ++ c)

def neonPairsResult (m : Memory) (i0 i1 o0 o1 : Address) (offset : Nat) : Nat → Memory
  | 0 => m
  | pairs + 1 => neonPairsResult (neonPairMemory m i0 i1 o0 o1)
      (i0 + BitVec.ofNat 64 offset) (i1 + BitVec.ofNat 64 offset)
      (o0 + 8#64) (o1 + 8#64) offset pairs

theorem NeonPairsSafe.advance {m : Memory} {i0 i1 o0 o1 : Address} {offset pairs : Nat}
    (h : NeonPairsSafe m i0 i1 o0 o1 offset (pairs+1)) :
    NeonPairsSafe (neonPairMemory m i0 i1 o0 o1)
      (i0 + BitVec.ofNat 64 offset) (i1 + BitVec.ofNat 64 offset)
      (o0 + 8#64) (o1 + 8#64) offset pairs := by
  constructor
  · intro r hr p hp
    simpa only [neonPairMemory, writeBytes_readable] using
      h.readable0 (r+1) (by omega) p (by simpa only [rowAddress_succ] using hp)
  · intro r hr p hp
    simpa only [neonPairMemory, writeBytes_readable] using
      h.readable1 (r+1) (by omega) p (by simpa only [rowAddress_succ] using hp)
  · intro r hr p hp
    simpa only [neonPairMemory, writeBytes_writable] using
      h.writable0 (r+1) (by omega) p (by simpa only [rowAddress_succ] using hp)
  · intro r hr p hp
    simpa only [neonPairMemory, writeBytes_writable] using
      h.writable1 (r+1) (by omega) p (by simpa only [rowAddress_succ] using hp)

theorem neonRowAfter_locals (s : State) (n offset : Nat) (i0 i1 o0 o1 : Address)
    (a b c d : List Byte) (m1 m2 : Memory) (h : NeonRowLocals s n offset i0 i1 o0 o1) :
    NeonRowLocals (neonRowAfter s n offset i0 i1 o0 o1 a b c d m1 m2) (n-2) offset
      (i0 + BitVec.ofNat 64 offset) (i1 + BitVec.ofNat 64 offset) (o0 + 8#64) (o1 + 8#64) := by
  constructor <;> simp [neonRowAfter, update, h.inputOffset, h.outputOffset]

/-- The actual unbounded NEON pair loop. Its intermediate result retains the
source store order, so this lemma also covers aliased output columns. -/
theorem neon_pairs_total (cfg : Config) (s : State) (pairs tail offset : Nat)
    (i0 i1 o0 o1 : Address) (small : tail < 2)
    (locals : NeonRowLocals s (2*pairs+tail) offset i0 i1 o0 o1)
    (bound : 2*pairs+tail < 2^64) (safe : NeonPairsSafe s.memory i0 i1 o0 o1 offset pairs) :
    ∃ t, Exec cfg neonRows s t ∧ t.memory = neonPairsResult s.memory i0 i1 o0 o1 offset pairs ∧
      NeonRowLocals t tail offset (rowAddress i0 offset pairs) (rowAddress i1 offset pairs)
        (rowAddress o0 8 pairs) (rowAddress o1 8 pairs) := by
  induction pairs generalizing s i0 i1 o0 o1 with
  | zero =>
    refine ⟨s, ?_, rfl, ?_⟩
    · apply Exec.done (v := .integer 0)
      · simp [neonRows, neonOuterBody, neonOuter, firstStatement, dropStatements,
          Generated.X32Transpose.neon, eval, binary, locals.height,
          show convert .u64 2 = 2 by decide, show (tail : Int) < 2 by omega]
      · rfl
    · simpa [rowAddress] using locals
  | succ pairs ih =>
    let a := readBytes s.memory i0 4
    let b := readBytes s.memory (i0 + 4#64) 4
    let c := readBytes s.memory i1 4
    let d := readBytes s.memory (i1 + 4#64) 4
    let m1 := writeBytes s.memory o1 (b ++ d)
    let m2 := writeBytes m1 o0 (a ++ c)
    have load0 : loadBytes s.memory i0 8 = some (a ++ b) := by
      rw [loadBytes_success _ _ _ (fun p hp => safe.readable0 0 (by omega) p (by simpa [rowAddress] using hp))]
      exact congrArg some (readBytes_add s.memory i0 4 4)
    have load1 : loadBytes s.memory i1 8 = some (c ++ d) := by
      rw [loadBytes_success _ _ _ (fun p hp => safe.readable1 0 (by omega) p (by simpa [rowAddress] using hp))]
      exact congrArg some (readBytes_add s.memory i1 4 4)
    have store1 : storeBytes s.memory o1 (b ++ d) = some m1 := by
      apply storeBytes_success
      intro p hp
      exact safe.writable1 0 (by omega) p (by simpa [rowAddress, b, d] using hp)
    have store0 : storeBytes m1 o0 (a ++ c) = some m2 := by
      apply storeBytes_success
      intro p hp
      simpa only [m1, writeBytes_writable] using
        safe.writable0 0 (by omega) p (by simpa [rowAddress, a, c] using hp)
    let u := neonRowAfter s (2*(pairs+1)+tail) offset i0 i1 o0 o1 a b c d m1 m2
    have hu : Exec cfg neonRowBody s u := neon_row_exec cfg s _ offset i0 i1 o0 o1
      a b c d m1 m2 locals (by omega) bound (readBytes_length ..) (readBytes_length ..)
      (readBytes_length ..) (readBytes_length ..) load0 load1 store1 store0
    have hl : NeonRowLocals u (2*pairs+tail) offset (i0 + BitVec.ofNat 64 offset)
        (i1 + BitVec.ofNat 64 offset) (o0 + 8#64) (o1 + 8#64) := by
      have he : 2*(pairs+1)+tail-2 = 2*pairs+tail := by omega
      simpa only [he] using neonRowAfter_locals s (2*(pairs+1)+tail) offset i0 i1 o0 o1
        a b c d m1 m2 locals
    obtain ⟨t, ht, hm, hf⟩ := ih u _ _ _ _ hl (by omega) safe.advance
    refine ⟨t, ?_, hm, ?_⟩
    · apply Exec.more (v := .integer 1) (t := u)
      · simp [neonRows, neonOuterBody, neonOuter, firstStatement, dropStatements,
          Generated.X32Transpose.neon, eval, binary, locals.height,
          show convert .u64 2 = 2 by decide, show (2 : Int) ≤ 2*(pairs+1)+tail by omega]
      · rfl
      · exact hu
      · exact ht
    · simpa only [rowAddress_succ] using hf

end Salty.Kernels.X32Transpose
