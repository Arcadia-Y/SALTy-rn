import Salty.Proofs.Rdsum.ChannelMemory

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

theorem readWords32_add (m : Memory) (output : Address) (left right : Nat) :
    readWords32 m output (left+right) = readWords32 m output left ++
      readWords32 m (output+BitVec.ofNat 64 (4*left)) right := by
  simp only [readWords32_columns, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_def, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

theorem storedWords_append (m : Memory) (output : Address) (left right : List (BitVec 32)) :
    storedWords m output (left.length+right.length) (left++right) =
      storedWords m output left.length left ++
      storedWords m (output+BitVec.ofNat 64 (4*left.length)) right.length right := by
  simp only [storedWords, readWords32_add]
  exact List.zipWith_append (by simp)

/-- Adjacent vector stores join even when their old values were loaded first. -/
theorem storedWords_write_join (m : Memory) (output : Address) (left right : List (BitVec 32)) :
    writeBytes (writeBytes m output (encodeWords32 (storedWords m output left.length left)))
      (output+BitVec.ofNat 64 (4*left.length))
      (encodeWords32 (storedWords m (output+BitVec.ofNat 64 (4*left.length)) right.length right)) =
    writeBytes m output (encodeWords32 (storedWords m output (left.length+right.length) (left++right))) := by
  rw [storedWords_append, encodeWords32_append, writeBytes_append]
  simp

end Salty.Kernels.Rdsum
