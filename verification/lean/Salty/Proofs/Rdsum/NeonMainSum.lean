import Salty.Proofs.Rdsum.NeonMainWiden

namespace Salty.Kernels.Rdsum
open CByte ReductionISA

def wordValues (initial : Nat → BitVec 32) (word : Nat) : List (BitVec 32) :=
  (List.range 4).map (fun lane => initial (4*word+lane))

def chunkValues (initial : Nat → BitVec 32) (chunk : Nat) : List (BitVec 32) :=
  (List.range 8).map (fun lane => initial (8*chunk+lane))

def zeroMainAcc : Nat → List (BitVec 16) := fun _ => (List.range 8).map (fun _ => 0)

theorem intervalSum_shift (kind : Interpretation) (m : Memory) (input : Address)
    (stride first rows start column : Nat) :
    intervalSum kind m (input+BitVec.ofNat 64 start) stride first rows column =
      intervalSum kind m input stride first rows (start+column) := by
  unfold intervalSum
  congr 2
  apply List.map_congr_left
  intro row hr
  congr 1
  simp only [BitVec.ofNat_add, BitVec.add_assoc]
  ac_rfl

theorem widen_mainFold_chunk (kind : Interpretation) (m : Memory) (input zero : Address)
    (stride count first rows chunk : Nat) (pointers : Nat → Address) (initial : Nat → BitVec 32)
    (counted : GroupCount count rows) (small : 7*count ≤ 256)
    (zeros : ∀ column, column < 8*chunk+8 → m.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < rows → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    WideningISA.widenAdd32 kind (chunkValues initial chunk)
      ((mainFold kind m zero (7*stride) count pointers rows zeroMainAcc).acc chunk) =
      chunkValues (fun column => initial column+intervalSum kind m input stride first rows column) chunk := by
  have exactSum := widen_groupFold_original kind m (input+BitVec.ofNat 64 (8*chunk))
    (zero+BitVec.ofNat 64 (8*chunk)) 8 stride count first rows
    (fun i => pointers i+BitVec.ofNat 64 (8*chunk)) (fun i => initial (8*chunk+i)) counted small
    (fun column hc => by
      have h := zeros (8*chunk+column) (by omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h)
    (fun i hi live => by dsimp only; rw [ptrs i hi live]; ac_rfl)
  have fold := mainFold_chunk kind m zero (7*stride) count pointers rows zeroMainAcc chunk
  simp only [zeroMainAcc] at fold
  rw [fold] at exactSum
  simpa only [chunkValues, intervalSum_shift] using exactSum

theorem wordValues_low (initial : Nat → BitVec 32) (word : Nat) (even : word % 2 = 0) :
    wordValues initial word = (chunkValues initial (word/2)).take 4 := by
  have offset : 4*word = 8*(word/2) := by omega
  have take (f : Nat → BitVec 32) : ((List.range 8).map f).take 4 = (List.range 4).map f := by rfl
  simp only [wordValues, chunkValues, take, offset]

theorem wordValues_high (initial : Nat → BitVec 32) (word : Nat) (odd : word % 2 ≠ 0) :
    wordValues initial word = (chunkValues initial (word/2)).drop 4 := by
  have offset : 4*word = 8*(word/2)+4 := by omega
  have drop (f : Nat → BitVec 32) : ((List.range 8).map f).drop 4 =
      (List.range 4).map (fun i => f (4+i)) := by rfl
  simp only [wordValues, chunkValues, drop, offset, Nat.add_assoc]

theorem mainWidenWord_parts (kind : Interpretation) (initial : Nat → BitVec 32)
    (half : Nat → List (BitVec 16)) (word : Nat) :
    mainWidenWord kind (wordValues initial) half word =
      if word % 2 = 0 then
        (WideningISA.widenAdd32 kind (chunkValues initial (word/2)) (half (word/2))).take 4
      else (WideningISA.widenAdd32 kind (chunkValues initial (word/2)) (half (word/2))).drop 4 := by
  by_cases even : word % 2 = 0
  · simp only [mainWidenWord, if_pos even, wordValues_low initial word even,
      WideningISA.widenAdd32, List.take_zipWith]
  · simp only [mainWidenWord, if_neg even, wordValues_high initial word even,
      WideningISA.widenAdd32, List.drop_zipWith]

/-- Each four-word source widening result is the corresponding original
column interval, including row padding and 16-bit batch bounds. -/
theorem widen_mainFold_word (kind : Interpretation) (m : Memory) (input zero : Address)
    (stride count first rows word : Nat) (pointers : Nat → Address) (initial : Nat → BitVec 32)
    (counted : GroupCount count rows) (small : 7*count ≤ 256)
    (zeros : ∀ column, column < 8*(word/2)+8 → m.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < rows → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    mainWidenWord kind (wordValues initial)
      (mainFold kind m zero (7*stride) count pointers rows zeroMainAcc).acc word =
      wordValues (fun column => initial column+intervalSum kind m input stride first rows column) word := by
  rw [mainWidenWord_parts, widen_mainFold_chunk kind m input zero stride count first rows (word/2) pointers initial counted small zeros ptrs]
  split
  next even => exact (wordValues_low _ word even).symm
  next odd => exact (wordValues_high _ word odd).symm

end Salty.Kernels.Rdsum
