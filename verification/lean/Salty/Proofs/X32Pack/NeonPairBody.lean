import Salty.Proofs.X32Pack.NeonDefs

namespace Salty.Kernels.X32Pack
open CByte

def packLow (xs ys : List Byte) : List Byte := xs.take 4 ++ ys.take 4
def packHigh (xs ys : List Byte) : List Byte := xs.drop 4 ++ ys.drop 4

theorem packLow_length (xs ys : List Byte) (hx : xs.length = 8) (hy : ys.length = 8) :
    (packLow xs ys).length = 8 := by simp [packLow, hx, hy]
theorem packHigh_length (xs ys : List Byte) (hx : xs.length = 8) (hy : ys.length = 8) :
    (packHigh xs ys).length = 8 := by simp [packHigh, hx, hy]

theorem pairBytes_two (m : Memory) (a b : Address) :
    pairBytes m a b 2 = packLow (readBytes m a 8) (readBytes m b 8) ++
      packHigh (readBytes m a 8) (readBytes m b 8) := by
  have takeDrop (base : Address) : ((readBytes m base 8).drop 4).take 4 = (readBytes m base 8).drop 4 := by
    apply List.take_of_length_le
    simp
  simp [pairBytes, interleaveWords, packLow, packHigh, takeDrop, List.append_assoc]

def neonPairAfter (s : State) (n : Nat) (a b output : Address) (x y : List Byte) : State :=
  let xs := readBytes s.memory a 8
  let ys := readBytes s.memory b 8
  let t := update s "v00" (.vectors 4 [replaceWord x (xs.take 4) 0, replaceWord y (xs.drop 4) 0])
  let t := update t "w0" (.pointer (a+8))
  let t := update t "v00" (.vectors 4 [packLow xs ys, packHigh xs ys])
  let t := update t "w1" (.pointer (b+8))
  let t := { t with memory := pairResult s.memory a b output 2 }
  let t := update t "packed_weights" (.pointer (output+16))
  update t "k" (.integer (n-2 : Nat))

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem neon_pair_body_exec (cfg : Config) (s : State) (n : Nat) (a b output : Address) (x y : List Byte)
    (loc : NeonPairLocals s n a b output x y) (hx : x.length = 8) (hy : y.length = 8)
    (enough : 2 ≤ n) (bound : 8*n ≤ 2^64) (safe : PairSafe s.memory a b output n) :
    Exec cfg neonPairBody s (neonPairAfter s n a b output x y) := by
  let xs := readBytes s.memory a 8
  let ys := readBytes s.memory b 8
  have hxs : xs.length = 8 := by simp [xs]
  have hys : ys.length = 8 := by simp [ys]
  have loLen : (packLow xs ys).length = 8 := packLow_length xs ys hxs hys
  have hiLen : (packHigh xs ys).length = 8 := packHigh_length xs ys hxs hys
  have loadA : loadBytes s.memory a 8 = some xs :=
    loadBytes_success _ _ _ (fun p hp => safe.readA p (footprint_mono (by omega) hp))
  have loadB : loadBytes s.memory b 8 = some ys :=
    loadBytes_success _ _ _ (fun p hp => safe.readB p (footprint_mono (by omega) hp))
  have firstCall : intrinsic cfg s.memory .load2LaneU32x2 [.pointer a, .vectors 4 [x,y], .integer 0] =
      some (.vectors 4 [replaceWord x (xs.take 4) 0, replaceWord y (xs.drop 4) 0]) := by
    simp [intrinsic, tupleMemoryIntrinsic, hx, hy, loadA]
  have secondCall : intrinsic cfg s.memory .load2LaneU32x2
      [.pointer b, .vectors 4 [replaceWord x (xs.take 4) 0, replaceWord y (xs.drop 4) 0], .integer 1] =
      some (.vectors 4 [packLow xs ys, packHigh xs ys]) := by
    have both := load2_pair cfg s.memory a b x y xs ys hx hy hxs loadA loadB
    simpa only [firstCall, Option.bind_some, packLow, packHigh] using both
  let middle := writeBytes s.memory output (packLow xs ys)
  have firstStore : effect s.memory .storeU32x2 [.pointer output, .vector 4 (packLow xs ys)] = some middle := by
    simp only [effect, storeVector, loLen, and_self, ↓reduceIte]
    apply storeBytes_success
    intro p hp
    exact safe.writable p (footprint_mono (by rw [loLen]; omega) hp)
  have secondStore : effect middle .storeU32x2 [.pointer (output+8#64), .vector 4 (packHigh xs ys)] =
      some (pairResult s.memory a b output 2) := by
    have bytes := storeBytes_success middle (output+8) (packHigh xs ys) (by
      intro p hp
      simp only [middle, writeBytes_writable]
      exact safe.writable p (footprint_shift_within (start := 8) (by rw [hiLen]; omega) hp))
    have joined : writeBytes middle (output+8) (packHigh xs ys) = pairResult s.memory a b output 2 := by
      unfold pairResult
      rw [pairBytes_two, writeBytes_append]
      change _ = writeBytes middle (output+BitVec.ofNat 64 (packLow xs ys).length) (packHigh xs ys)
      rw [loLen]
      rfl
    rw [joined] at bytes
    simpa [effect, storeVector, hiLen] using bytes
  have sub : convert .u64 ((n : Int)-2) = (n-2 : Nat) := cast_sub n 2 enough (by omega)
  have subnorm : max (((n : Int)-2) % 18446744073709551616) 0 = (n-2 : Nat) := by simpa [convert] using sub
  rw [neon_pair_body_shape]
  apply run_sound (fuel := 24)
  simp +contextual [run, eval, binary, convert, update_memory, update_locals,
    loc.count, loc.left, loc.right, loc.output, loc.tuple, firstCall, secondCall, firstStore, secondStore,
    subnorm, show max (2 : Int) 0 = 2 by decide, neonPairAfter, xs, ys]

theorem neonPairAfter_memory (s : State) (n : Nat) (a b output : Address) (x y : List Byte) :
    (neonPairAfter s n a b output x y).memory = pairResult s.memory a b output 2 := rfl

theorem neonPairAfter_locals (s : State) (n : Nat) (a b output : Address) (x y : List Byte) :
    NeonPairLocals (neonPairAfter s n a b output x y) (n-2) (a+8) (b+8) (output+16)
      (packLow (readBytes s.memory a 8) (readBytes s.memory b 8))
      (packHigh (readBytes s.memory a 8) (readBytes s.memory b 8)) := by
  constructor <;> simp [neonPairAfter, update_locals]

end Salty.Kernels.X32Pack
