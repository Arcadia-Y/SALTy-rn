import Salty.Proofs.X32Pack.NeonPairTail

namespace Salty.Kernels.X32Pack
open CByte

def neonPairDepth : Stmt := takeStatements 2 (dropStatements 3 neonChannelBody)

theorem neon_pair_depth_shape : neonPairDepth = .seq neonPairLoop (.seq neonPairTail .skip) := rfl

/-- Complete paired-channel source depth traversal: the two-word loop followed
by its separate zero/one-word remainder loop. -/
theorem neon_pair_depth_total (cfg : Config) (s : State) (n : Nat) (a b output : Address) (x y : List Byte)
    (loc : NeonPairLocals s n a b output x y) (hx : x.length = 8) (hy : y.length = 8)
    (bound : 8*n ≤ 2^64) (safe : PairSafe s.memory a b output n) :
    ∃ t finalX finalY, Exec cfg neonPairDepth s t ∧ t.memory = pairResult s.memory a b output n ∧
      NeonPairLocals t 0 (a+BitVec.ofNat 64 (4*n)) (b+BitVec.ofNat 64 (4*n))
        (output+BitVec.ofNat 64 (8*n)) finalX finalY ∧ finalX.length = 8 ∧ finalY.length = 8 := by
  obtain ⟨u, r, mx, my, main, memory, locals, small, le, lenX, lenY⟩ :=
    neon_pair_loop_total cfg s n a b output x y loc hx hy bound safe
  have tailSafe : PairSafe u.memory (a+BitVec.ofNat 64 (4*(n-r))) (b+BitVec.ofNat 64 (4*(n-r)))
      (output+BitVec.ofNat 64 (8*(n-r))) r := by
    rw [memory]
    have h := safe.advance (show n-r ≤ n by omega) (pairBytes s.memory a b (n-r))
    rw [show n-(n-r) = r by omega] at h
    exact h
  obtain ⟨t, finalX, tail, tailMem, finalLoc, finalLength⟩ :=
    neon_pair_tail_total cfg u r (a+BitVec.ofNat 64 (4*(n-r))) (b+BitVec.ofNat 64 (4*(n-r)))
      (output+BitVec.ofNat 64 (8*(n-r))) mx my locals lenX lenY small tailSafe
  refine ⟨t, finalX, my, ?_, ?_, ?_, finalLength, lenY⟩
  · rw [neon_pair_depth_shape]
    exact .seq main (.seq tail .skip)
  · rw [tailMem, memory]
    have split := pairResult_split safe (show n-r ≤ n by omega)
    rw [show n-(n-r) = r by omega] at split
    exact split.symm
  · have address (base : Address) (width : Nat) :
        base+BitVec.ofNat 64 (width*(n-r))+BitVec.ofNat 64 (width*r) = base+BitVec.ofNat 64 (width*n) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add, show n-r+r = n by omega]
    rw [address a 4, address b 4, address output 8] at finalLoc
    exact finalLoc

end Salty.Kernels.X32Pack
