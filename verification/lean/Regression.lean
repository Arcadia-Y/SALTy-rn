import Salty.Examples.Rdsum
import Salty.Examples.X32Pack
import Salty.Examples.Rsum
import Salty.Examples.QU8Add
import Salty.Examples.QS8Add

-- Finite compiled evaluation, not a Lean equivalence theorem or proof oracle.
open Salty Salty.Kernels.QS8AddExamples
#eval show IO Unit from do
  for (shift, expected) in ([(0, 1), (1, 1), (2, 0), (31, 0), (32, 0),
      (33, 0), (127, 0), (128, 0), (224, 0), (225, 128), (255, 2)] : List (Byte × Byte)) do
    unless output Generated.QS8Add.neon shift == some expected do
      throw (IO.userError s!"extracted NEON quantized-add mismatch at shift {shift}")
    unless output Generated.QS8Add.rvv shift == some expected do
      throw (IO.userError s!"extracted RVV quantized-add mismatch at shift {shift}")
  IO.println "Finite extracted quantized-add executions: shift branches passed (not a whole-kernel proof)."

-- Finite compiled evaluation, not a Lean equivalence theorem or proof oracle.
open Salty Salty.Kernels.QU8AddExamples
#eval show IO Unit from do
  for (shift, expected) in ([(0, 1), (1, 1), (2, 0), (31, 0), (32, 0),
      (33, 0), (127, 0), (128, 0), (224, 0), (225, 0), (255, 2)] : List (Byte × Byte)) do
    unless Salty.Kernels.QU8AddExamples.output Generated.QU8Add.neon shift == some expected do
      throw (IO.userError s!"extracted NEON unsigned quantized-add mismatch at shift {shift}")
    unless Salty.Kernels.QU8AddExamples.output Generated.QU8Add.rvv shift == some expected do
      throw (IO.userError s!"extracted RVV unsigned quantized-add mismatch at shift {shift}")
  IO.println "Finite extracted unsigned quantized-add executions: shift branches passed (not a whole-kernel proof)."

-- Exact extracted control flow at tail/block boundaries; no proof oracle.
#eval show IO Unit from do
  let cases : List (Nat × Byte × Int) :=
    [(1, 128, 0), (15, 255, 7), (16, 127, -7), (17, 128, 0),
     (31, 255, 0), (32, 1, 0), (33, 127, 0), (2047, 128, 0),
     (2048, 128, 0), (2049, 255, 0), (4096, 255, 0), (4097, 127, 0)]
  let capacities : List {n : Nat // 0 < n} := [⟨32, by decide⟩, ⟨64, by decide⟩, ⟨128, by decide⟩]
  for capacity in capacities do
    for balanced in [false, true] do
      let cfg := Salty.Kernels.RsumExamples.config capacity.val capacity.property balanced
      for (n, byte, initial) in cases do
        let signedExpected := CByte.bytes32 (initial + n * byte.toInt)
        let unsignedExpected := CByte.bytes32 ((BitVec.ofInt 32 initial).toNat + n * (byte.toNat : Int))
        for code in [Generated.QS8Rsum.neon, Generated.QS8Rsum.rvv] do
          unless Salty.Kernels.RsumExamples.output cfg code n byte initial == some signedExpected do
            throw (IO.userError s!"signed extracted reduction mismatch: n={n}, byte={byte}, capacity={capacity.val}, balanced={balanced}")
        for code in [Generated.QU8Rsum.neon, Generated.QU8Rsum.rvv] do
          unless Salty.Kernels.RsumExamples.output cfg code n byte initial == some unsignedExpected do
            throw (IO.userError s!"unsigned extracted reduction mismatch: n={n}, byte={byte}, capacity={capacity.val}, balanced={balanced}")
      for code in [Generated.QS8Rsum.neon, Generated.QS8Rsum.rvv] do
        unless Salty.Kernels.RsumExamples.output cfg code 1 1 2147483647 == none do
          throw (IO.userError "signed output overflow was accepted")
      for code in [Generated.QU8Rsum.neon, Generated.QU8Rsum.rvv] do
        unless Salty.Kernels.RsumExamples.output cfg code 1 1 4294967295 == some (CByte.bytes32 0) do
          throw (IO.userError "unsigned output addition failed to wrap")
  IO.println "Finite extracted reductions: tails,2048byte blocks,shrinking VL,signed overflow,unsigned wrap passed (not a whole-kernel proof)."

-- Independent packed-layout oracle includes odd-channel holes and extra gaps.
#eval show IO Unit from do
  let cases : List (Nat × Nat × Nat) := [(1,1,1), (1,2,2), (1,3,3), (2,1,17),
    (2,4,15), (2,5,16), (1,3,31), (1,2,33), (2,3,65)]
  let capacities : List {n : Nat // 0 < n} := [⟨16, by decide⟩, ⟨32, by decide⟩, ⟨64, by decide⟩]
  for capacity in capacities do
    for balanced in [false, true] do
      let cfg := Salty.Kernels.RsumExamples.config capacity.val capacity.property balanced
      for (g,nc,kc) in cases do
        for extra in [0,12] do
          for withBias in [false,true] do
            for code in [Generated.X32Pack.neon, Generated.X32Pack.rvv] do
              unless Salty.Kernels.X32PackExamples.check cfg code g nc kc extra withBias do
                throw (IO.userError s!"packing layout mismatch: g={g}, nc={nc}, kc={kc}, extra={extra}, bias={withBias}, capacity={capacity.val}, balanced={balanced}")
  IO.println "Finite extracted packing: grouped layout, odd channels, null bias, gaps and VL policies passed (not a whole-kernel proof)."

