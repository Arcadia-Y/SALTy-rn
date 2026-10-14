import Salty.Proofs.Rdsum.WordMemory

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

/-- A written prefix leaves the old words in the remaining suffix unchanged. -/
theorem readWords32_after_prefix (m : Memory) (output : Address) (left right : Nat)
    (bs : List Byte) (len : bs.length = 4*left) (bound : 4*(left+right) < 2^64) :
    readWords32 (writeBytes m output bs) (output+BitVec.ofNat 64 (4*left)) right =
      readWords32 m (output+BitVec.ofNat 64 (4*left)) right := by
  simp only [readWords32_columns]
  apply List.map_congr_left
  intro i hi
  have ilt := List.mem_range.mp hi
  unfold readWord32
  rw [readBytes_writeBytes_disjoint]
  intro a ha
  rw [len]
  apply footprint_prefix_suffix output a (4*left) (4*right) (by omega)
  exact footprint_shift_within (by omega) ha

theorem readWord32_after_prefix_at (m : Memory) (output : Address) (left column : Nat)
    (bs : List Byte) (len : bs.length = 4*left) (bound : 4*(left+column+1) < 2^64) :
    readWord32 (writeBytes m output bs) (output+BitVec.ofNat 64 (4*left)+BitVec.ofNat 64 (4*column)) =
      readWord32 m (output+BitVec.ofNat 64 (4*left)+BitVec.ofNat 64 (4*column)) := by
  unfold readWord32
  rw [readBytes_writeBytes_disjoint]
  intro a ha
  rw [len]
  apply footprint_prefix_suffix output a (4*left) (4*(column+1)) (by omega)
  exact footprint_shift_within (by omega) ha

theorem readWord32_after_prefix (m : Memory) (output : Address) (left : Nat)
    (bs : List Byte) (len : bs.length = 4*left) (bound : 4*(left+1) < 2^64) :
    readWord32 (writeBytes m output bs) (output+BitVec.ofNat 64 (4*left)) =
      readWord32 m (output+BitVec.ofNat 64 (4*left)) := by
  have h := readWords32_after_prefix m output left 1 bs len bound
  simpa only [readWords32, List.cons.injEq, and_true] using h

/-- Sequential load/add/store chunks are the original-memory wordwise result. -/
theorem storedWords_write_join_after (m : Memory) (output : Address) (left right : List (BitVec 32))
    (bound : 4*(left.length+right.length) < 2^64) :
    let firstBytes := encodeWords32 (storedWords m output left.length left)
    let next := writeBytes m output firstBytes
    writeBytes next (output+BitVec.ofNat 64 (4*left.length))
      (encodeWords32 (storedWords next (output+BitVec.ofNat 64 (4*left.length)) right.length right)) =
    writeBytes m output (encodeWords32 (storedWords m output (left.length+right.length) (left++right))) := by
  dsimp only
  have frame := readWords32_after_prefix m output left.length right.length
    (encodeWords32 (storedWords m output left.length left)) (by simp) bound
  have unchanged : storedWords (writeBytes m output (encodeWords32 (storedWords m output left.length left)))
      (output+BitVec.ofNat 64 (4*left.length)) right.length right =
      storedWords m (output+BitVec.ofNat 64 (4*left.length)) right.length right := by
    exact congrArg (fun xs => List.zipWith (· + ·) xs right) frame
  rw [unchanged]
  exact storedWords_write_join m output left right

end Salty.Kernels.Rdsum
