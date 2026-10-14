import Salty.Proofs.X32Transpose.NeonTail
import Salty.Proofs.Core.MatrixSlices

namespace Salty.Kernels.X32Transpose
open CByte

/-- The exact nonaliased source tile refines the same matrix copy used by RVV.
The permutation exchanges the source's column-one-first store order for the
specification's row order, justified by byte-disjoint output words. -/
theorem neon_pair_matrix (m : Memory) (p : MatrixCopy)
    (sep : ({p with rows := 2, cols := 2} : MatrixCopy).separated) :
    neonPairMemory m p.input (p.input + BitVec.ofNat 64 p.inputStride)
      p.output (p.output + BitVec.ofNat 64 p.outputStride) =
      ({p with rows := 2, cols := 2} : MatrixCopy).result m := by
  let q : MatrixCopy := {p with rows := 2, cols := 2}
  let visits : List (Nat × Nat) := [(0,1),(1,1),(0,0),(1,0)]
  have actual : neonPairMemory m p.input (p.input + BitVec.ofNat 64 p.inputStride)
      p.output (p.output + BitVec.ofNat 64 p.outputStride) = visits.foldl (q.writeWord m) m := by
    simp [neonPairMemory, writeBytes_append, visits, MatrixCopy.writeWord,
      MatrixCopy.readAddress, MatrixCopy.writeAddress, q, BitVec.ofNat_add, BitVec.add_assoc]
  rw [actual]
  apply q.order_independent m m visits q.rowVisits sep
  · intro rc hrc
    simp only [visits, List.mem_cons, List.not_mem_nil, or_false] at hrc
    rcases hrc with rfl | rfl | rfl | rfl <;> simp [q, MatrixCopy.valid]
  · change [(0,1),(1,1),(0,0),(1,0)].Perm [(0,0),(0,1),(1,0),(1,1)]
    decide

/-- Aliasing both destination columns erases column one's transient writes;
exactly the first source column remains, including every surrounding byte. -/
theorem neon_pair_matrix_alias (m : Memory) (p : MatrixCopy) :
    neonPairMemory m p.input (p.input + BitVec.ofNat 64 p.inputStride) p.output p.output =
      ({p with rows := 2, cols := 1} : MatrixCopy).result m := by
  unfold neonPairMemory
  rw [writeBytes_overwrite _ _ _ _ (by simp)]
  simp [MatrixCopy.result, MatrixCopy.rowVisits, MatrixCopy.writeWord,
    MatrixCopy.readAddress, MatrixCopy.writeAddress, writeBytes_append, BitVec.ofNat_add,
    BitVec.add_assoc, List.range_succ]

end Salty.Kernels.X32Transpose
