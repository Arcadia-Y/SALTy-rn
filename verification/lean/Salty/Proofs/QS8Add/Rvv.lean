import Salty.Proofs.QS8Add.RvvBlocks

namespace Salty.Kernels.QS8Add
open CByte QuantizedAddISA
open SIMD.Arithmetic

structure RvvLocals (s : State) (n : Nat) (a b output : Address) (p : Params) : Prop where
  batch : s.locals "batch" = some (.integer n)
  inputA : s.locals "input_a" = some (.pointer a)
  inputB : s.locals "input_b" = some (.pointer b)
  outputPtr : s.locals "output" = some (.pointer output)
  zeroA : s.locals "a_zero_point" = some (.integer p.aZero.toInt)
  zeroB : s.locals "b_zero_point" = some (.integer p.bZero.toInt)
  multA : s.locals "a_multiplier" = some (.integer p.aMultiplier.toInt)
  multB : s.locals "b_multiplier" = some (.integer p.bMultiplier.toInt)
  shift : s.locals "shift" = some (.integer (ShiftISA.rvvCount p.shift))
  outputZero : s.locals "output_zero_point" = some (.integer p.outputZero.toInt)
  outputMin : s.locals "output_min" = some (.integer p.outputMin.toInt)
  outputMax : s.locals "output_max" = some (.integer p.outputMax.toInt)

def shiftAfter (s : State) (p : Params) (as bs : List Byte) : State :=
  update s "vacc" (.words32 ((List.zipWith (rvvProduct p) as bs).map
    (fun x => ShiftISA.repairedShift x p.shift)))

def bodyAfter (s : State) (n k : Nat) (a b output : Address) (p : Params)
    (as bs : List Byte) (m : Memory) : State :=
  let loaded := loadAfter s k as bs
  let widened := wideAfter loaded p as bs
  let multiplied := productAfter widened p as bs
  let shifted := shiftAfter multiplied p as bs
  let converted := convertAfter shifted p ((List.zipWith (rvvProduct p) as bs).map
    (fun x => ShiftISA.repairedShift x p.shift))
  storeAfter converted n k a b output m

theorem output_lanes (p : Params) (as bs : List Byte) :
    ((List.zipWith (rvvProduct p) as bs).map (fun x => ShiftISA.repairedShift x p.shift)).map
      (rvvFinish p) = List.zipWith (rvvLane p) as bs := by
  simp only [List.map_map, List.map_zipWith, Function.comp_def, rvvFinish_product]

set_option maxHeartbeats 1000000 in
theorem rvv_body_exec (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (as bs : List Byte) (m : Memory)
    (locals : RvvLocals s n a b output p) (bound : n < 2^64)
    (ha : as.length = cfg.choose n) (hb : bs.length = cfg.choose n)
    (la : loadBytes s.memory a (cfg.choose n) = some as)
    (lb : loadBytes s.memory b (cfg.choose n) = some bs)
    (store : storeBytes s.memory output (List.zipWith (rvvLane p) as bs) = some m) :
    Exec cfg rvvBody s (bodyAfter s n (cfg.choose n) a b output p as bs m) := by
  let k := cfg.choose n
  let loaded := loadAfter s k as bs
  let widened := wideAfter loaded p as bs
  let multiplied := productAfter widened p as bs
  let shifted := shiftAfter multiplied p as bs
  let xs := (List.zipWith (rvvProduct p) as bs).map (fun x => ShiftISA.repairedShift x p.shift)
  let converted := convertAfter shifted p xs
  have xlen : xs.length = k := by simp [xs, ha, hb, k]
  have cap : k ≤ cfg.capacity := Nat.le_trans (cfg.bounded n) (Nat.min_le_right ..)
  have le : k ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
  have load : Exec cfg (takeStatements 3 rvvBody) s loaded :=
    rvv_load_exec cfg s n a b as bs locals.batch locals.inputA locals.inputB la lb
  have wide : Exec cfg (takeStatements 4 (dropStatements 3 rvvBody)) loaded widened :=
    rvv_wide_exec cfg loaded p as bs k
      (by simp [loaded, loadAfter, update])
      (by simp [loaded, loadAfter, update])
      (by simp [loaded, loadAfter, update])
      (by simp [loaded, loadAfter, update, locals.zeroA])
      (by simp [loaded, loadAfter, update, locals.zeroB]) ha hb
  have product : Exec cfg (takeStatements 2 (dropStatements 7 rvvBody)) widened multiplied :=
    rvv_product_exec cfg widened p as bs k
      (by simp [widened, loaded, wideAfter, loadAfter, update])
      (by simp [widened, wideAfter, update])
      (by simp [widened, wideAfter, update])
      (by simp [widened, loaded, wideAfter, loadAfter, update, locals.multA])
      (by simp [widened, loaded, wideAfter, loadAfter, update, locals.multB]) ha hb
  have shift : Exec cfg rvvShiftBlock multiplied shifted :=
    rvv_shift_exec cfg multiplied p.shift (List.zipWith (rvvProduct p) as bs) k
      (by simp [multiplied, widened, loaded, productAfter, wideAfter, loadAfter, update, locals.shift])
      (by simp [multiplied, productAfter, update])
      (by simp [multiplied, widened, loaded, productAfter, wideAfter, loadAfter, update])
      (by simp [ha, hb, k]) cap
  have convert : Exec cfg (takeStatements 5 (dropStatements 10 rvvBody)) shifted converted :=
    rvv_convert_exec cfg shifted p xs k
      (by simp [shifted, multiplied, widened, loaded, shiftAfter, productAfter, wideAfter, loadAfter, update])
      (by simp [shifted, shiftAfter, update, xs])
      (by simp [shifted, multiplied, widened, loaded, shiftAfter, productAfter, wideAfter, loadAfter, update, locals.outputZero])
      (by simp [shifted, multiplied, widened, loaded, shiftAfter, productAfter, wideAfter, loadAfter, update, locals.outputMin])
      (by simp [shifted, multiplied, widened, loaded, shiftAfter, productAfter, wideAfter, loadAfter, update, locals.outputMax]) xlen
  have stored : Exec cfg (dropStatements 15 rvvBody) converted
      (bodyAfter s n k a b output p as bs m) :=
    rvv_store_exec cfg converted n k a b output (xs.map (rvvFinish p)) m bound le
      (by simp [converted, shifted, multiplied, widened, loaded, convertAfter, shiftAfter, productAfter, wideAfter, loadAfter, update, locals.batch])
      (by simp [converted, shifted, multiplied, widened, loaded, convertAfter, shiftAfter, productAfter, wideAfter, loadAfter, update])
      (by simp [converted, shifted, multiplied, widened, loaded, convertAfter, shiftAfter, productAfter, wideAfter, loadAfter, update, locals.inputA])
      (by simp [converted, shifted, multiplied, widened, loaded, convertAfter, shiftAfter, productAfter, wideAfter, loadAfter, update, locals.inputB])
      (by simp [converted, shifted, multiplied, widened, loaded, convertAfter, shiftAfter, productAfter, wideAfter, loadAfter, update, locals.outputPtr])
      (by simp [converted, convertAfter, update]) (by simp [xlen])
      (by simpa only [converted, shifted, multiplied, widened, loaded, convertAfter, shiftAfter,
        productAfter, wideAfter, loadAfter, update, xs, output_lanes] using store)
  have rest : Exec cfg (dropStatements 9 rvvBody) multiplied
      (bodyAfter s n k a b output p as bs m) :=
    Exec.seq shift (exec_take_drop 5 convert stored)
  exact exec_take_drop 3 load (exec_take_drop 4 wide (exec_take_drop 2 product rest))

theorem bodyAfter_locals (s : State) (n k : Nat) (a b output : Address) (p : Params)
    (as bs : List Byte) (m : Memory) (h : RvvLocals s n a b output p) :
    RvvLocals (bodyAfter s n k a b output p as bs m) (n - k)
      (a + BitVec.ofNat 64 k) (b + BitVec.ofNat 64 k) (output + BitVec.ofNat 64 k) p := by
  constructor <;> simp [bodyAfter, storeAfter, convertAfter, shiftAfter, productAfter,
    wideAfter, loadAfter, update, h.zeroA, h.zeroB, h.multA, h.multB, h.shift,
    h.outputZero, h.outputMin, h.outputMax]

/-- The actual scalable loop terminates for every admissible byte count and
bounded progressing VL schedule. Both inputs are read from original memory. -/
theorem rvv_loop_total (cfg : Config) (s : State) (n : Nat) (a b output : Address)
    (p : Params) (locals : RvvLocals s n a b output p) (bound : n < 2^64)
    (safe : BinarySafe s.memory a b output n 0) :
    ∃ t, Exec cfg rvvLoop s t ∧ t.memory = binaryResult (rvvLane p) s.memory a b output n := by
  by_cases zero : n = 0
  · subst n
    refine ⟨s, ?_, rfl⟩
    apply Exec.done (v := .integer 0)
    · simp [rvvLoop, firstStatement, dropStatements, Generated.QS8Add.rvv, eval, binary, convert, locals.batch]
    · rfl
  · let k := cfg.choose n
    have pos : 0 < k := cfg.positive n (by omega)
    have le : k ≤ n := Nat.le_trans (cfg.bounded n) (Nat.min_le_left ..)
    let as := readBytes s.memory a k
    let bs := readBytes s.memory b k
    let written := List.zipWith (rvvLane p) as bs
    let m := writeBytes s.memory output written
    let next := bodyAfter s n k a b output p as bs m
    have len : written.length = k := by simp [written, as, bs]
    have la : loadBytes s.memory a k = some as :=
      loadBytes_success _ _ _ (fun x hx => safe.readA x (footprint_mono (by omega) hx))
    have lb : loadBytes s.memory b k = some bs :=
      loadBytes_success _ _ _ (fun x hx => safe.readB x (footprint_mono (by omega) hx))
    have store : storeBytes s.memory output written = some m :=
      storeBytes_success _ _ _ (fun x hx => safe.writable x (footprint_mono (by omega) hx))
    have body : Exec cfg rvvBody s next := rvv_body_exec cfg s n a b output p as bs m locals bound
      (readBytes_length ..) (readBytes_length ..) la lb store
    have nextlocals := bodyAfter_locals s n k a b output p as bs m locals
    have nextsafe := safe.advance le written
    obtain ⟨t, hr, hm⟩ := rvv_loop_total cfg next (n-k)
      (a + BitVec.ofNat 64 k) (b + BitVec.ofNat 64 k) (output + BitVec.ofNat 64 k)
      p nextlocals (by omega) nextsafe
    refine ⟨t, ?_, ?_⟩
    · apply Exec.more (v := .integer 1) (t := next)
      · simp [rvvLoop, firstStatement, dropStatements, Generated.QS8Add.rvv, eval, binary,
          convert, locals.batch, zero, show (0 : Int) < n by omega]
      · rfl
      · exact body
      · exact hr
    · rw [hm]
      exact (binaryResult_split (rvvLane p) safe le).symm
termination_by n

end Salty.Kernels.QS8Add
