import Salty.Examples.Rdsum
open Salty

-- Row sums remain unproved whole functions; these independently check the new
-- extraction against scalar column sums, including row/channel tails.
def main : IO Unit := do
  let cases : List (Nat × Nat) := (List.range 33).map (fun i => (8,i+1)) ++
    [(1,3), (2,7), (6,17), (7,32), (251,9), (252,33), (253,65), (504,16), (505,31)]
  let capacities : List {n : Nat // 0 < n} := [⟨32, by decide⟩, ⟨64, by decide⟩]
  for capacity in capacities do
    for balanced in [false,true] do
      let cfg := Salty.Kernels.RsumExamples.config capacity.val capacity.property balanced
      for (rows,channels) in cases do
        for code in [Generated.QS8Rdsum.neon, Generated.QS8Rdsum.rvv] do
          unless Salty.Kernels.RdsumExamples.check cfg code true rows channels 17 do
            throw (IO.userError s!"signed row-sum mismatch: rows={rows}, channels={channels}, capacity={capacity.val}, balanced={balanced}")
        for code in [Generated.QU8Rdsum.neon, Generated.QU8Rdsum.rvv] do
          unless Salty.Kernels.RdsumExamples.check cfg code false rows channels 4294967280 do
            throw (IO.userError s!"unsigned row-sum mismatch: rows={rows}, channels={channels}, capacity={capacity.val}, balanced={balanced}")
      unless (CByte.run cfg 8192 Generated.QS8Rdsum.neon (Salty.Kernels.RdsumExamples.state 1 1 (-2147483648))).isNone do
        throw (IO.userError "signed scalar row-sum overflow accepted")
      unless Salty.Kernels.RdsumExamples.check cfg Generated.QS8Rdsum.rvv true 1 1 (-2147483648) do
        throw (IO.userError "RVV row-sum vector wrap mismatch")
  IO.println "Finite extracted row sums: seven-row and252-row batches, channel tails, zero substitution, VL policies and scalar overflow boundary passed (not a whole-kernel proof)."
