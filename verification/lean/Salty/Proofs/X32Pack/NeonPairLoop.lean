import Salty.Proofs.X32Pack.NeonPairBody

namespace Salty.Kernels.X32Pack
open CByte

/-- The source's two-depth loop writes every full pair and leaves zero or one
word from each input stream for the separate scalar-lane remainder loop. -/
theorem neon_pair_loop_total (cfg : Config) (s : State) (n : Nat) (a b output : Address) (x y : List Byte)
    (loc : NeonPairLocals s n a b output x y) (hx : x.length = 8) (hy : y.length = 8)
    (bound : 8*n ≤ 2^64) (safe : PairSafe s.memory a b output n) :
    ∃ t r finalX finalY, Exec cfg neonPairLoop s t ∧
      t.memory = pairResult s.memory a b output (n-r) ∧
      NeonPairLocals t r (a+BitVec.ofNat 64 (4*(n-r))) (b+BitVec.ofNat 64 (4*(n-r)))
        (output+BitVec.ofNat 64 (8*(n-r))) finalX finalY ∧
      r < 2 ∧ r ≤ n ∧ finalX.length = 8 ∧ finalY.length = 8 := by
  induction n using Nat.strongRecOn generalizing s a b output x y with
  | ind n ih =>
    by_cases enough : 2 ≤ n
    · let next := neonPairAfter s n a b output x y
      let xs := packLow (readBytes s.memory a 8) (readBytes s.memory b 8)
      let ys := packHigh (readBytes s.memory a 8) (readBytes s.memory b 8)
      have body : Exec cfg neonPairBody s next := neon_pair_body_exec cfg s n a b output x y loc hx hy enough bound safe
      have memory : next.memory = pairResult s.memory a b output 2 := rfl
      have locals : NeonPairLocals next (n-2) (a+8) (b+8) (output+16) xs ys := neonPairAfter_locals ..
      have lengthX : xs.length = 8 := packLow_length _ _ (by simp) (by simp)
      have lengthY : ys.length = 8 := packHigh_length _ _ (by simp) (by simp)
      have nextSafe : PairSafe next.memory (a+8) (b+8) (output+16) (n-2) :=
        safe.advance enough (pairBytes s.memory a b 2)
      obtain ⟨t, r, finalX, finalY, execution, result, finalLoc, small, le, lenX, lenY⟩ :=
        ih (n-2) (by omega) next (a+8) (b+8) (output+16) xs ys locals lengthX lengthY (by omega) nextSafe
      refine ⟨t, r, finalX, finalY, ?_, ?_, ?_, small, by omega, lenX, lenY⟩
      · rw [neon_pair_loop_shape] at execution ⊢
        apply Exec.more (v := .integer 1) (t := next)
        · simp [eval, binary, convert, loc.count, show max (2 : Int) 0 = 2 by decide,
            show (2 : Int) ≤ n by omega]
        · rfl
        · exact body
        · exact execution
      · rw [result, memory]
        have split := pairResult_split (safe.prefix (show n-r ≤ n by omega)) (show 2 ≤ n-r by omega)
        have count : n-r-2 = n-2-r := by omega
        rw [count] at split
        exact split.symm
      · have address (base : Address) (width : Nat) :
            base+BitVec.ofNat 64 (width*2)+BitVec.ofNat 64 (width*(n-2-r)) =
              base+BitVec.ofNat 64 (width*(n-r)) := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]
          rw [show 2+(n-2-r) = n-r by omega]
        change NeonPairLocals t r
          (a+BitVec.ofNat 64 (4*2)+BitVec.ofNat 64 (4*(n-2-r)))
          (b+BitVec.ofNat 64 (4*2)+BitVec.ofNat 64 (4*(n-2-r)))
          (output+BitVec.ofNat 64 (8*2)+BitVec.ofNat 64 (8*(n-2-r))) finalX finalY at finalLoc
        rw [address a 4, address b 4, address output 8] at finalLoc
        exact finalLoc
    · refine ⟨s, n, x, y, ?_, ?_, ?_, by omega, Nat.le_refl n, hx, hy⟩
      · rw [neon_pair_loop_shape]
        apply Exec.done (v := .integer 0)
        · simp [eval, binary, convert, loc.count, show max (2 : Int) 0 = 2 by decide,
            show ¬ (2 : Int) ≤ n by omega]
        · rfl
      · simp [pairResult, pairBytes, interleaveWords, writeBytes]
      · simpa using loc

end Salty.Kernels.X32Pack
