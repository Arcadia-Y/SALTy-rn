import Salty.Proofs.Core.CByte

/-! Connections between checked CByte instruction calls and the reduction lane
lemmas. These are instruction results, not whole-function equivalence claims. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace Salty.CByte
open ReductionISA

def pair16Prim : Interpretation → Prim
  | .signed => .pairAcc16S
  | .unsigned => .pairAcc16U

def pair32Prim : Interpretation → Prim
  | .signed => .pairAcc32S
  | .unsigned => .pairAcc32U

def reduce32Prim : Interpretation → Prim
  | .signed => .reduceI32x4S
  | .unsigned => .reduceI32x4U

def extendByte32Prim : Interpretation → Prim
  | .signed => .extendByte32RVVS
  | .unsigned => .extendByte32RVVU

def scalar32Prim : Interpretation → Prim
  | .signed => .scalarI32RVVS
  | .unsigned => .scalarI32RVVU

theorem pair16_intrinsic (cfg : Config) (m : Memory) (kind : Interpretation)
    (acc : List (BitVec 16)) (xs : List Byte) (ha : acc.length = 8) (hx : xs.length = 16) :
    intrinsic cfg m (pair16Prim kind) [.halfwords acc, .vector 1 xs] =
      some (.halfwords (pairAcc16 kind acc xs)) := by
  cases kind <;> simp [pair16Prim, intrinsic, reductionIntrinsic, ha, hx]

theorem pair32_intrinsic (cfg : Config) (m : Memory) (kind : Interpretation)
    (acc : List (BitVec 32)) (xs : List (BitVec 16)) (ha : acc.length = 4) (hx : xs.length = 8) :
    intrinsic cfg m (pair32Prim kind) [.words32 acc, .halfwords xs] =
      some (.words32 (pairAcc32 kind acc xs)) := by
  cases kind <;> simp [pair32Prim, intrinsic, reductionIntrinsic, ha, hx]

theorem neon_reduce_intrinsic (cfg : Config) (m : Memory) (kind : Interpretation)
    (xs : List (BitVec 32)) (hx : xs.length = 4) :
    intrinsic cfg m (reduce32Prim kind) [.words32 xs] = some (.integer (value kind (sumWords xs))) := by
  cases kind <;> simp [reduce32Prim, intrinsic, reductionIntrinsic, hx]

theorem extend_byte_intrinsic (cfg : Config) (m : Memory) (kind : Interpretation)
    (xs : List Byte) (hx : xs.length ≤ cfg.capacity) :
    intrinsic cfg m (extendByte32Prim kind) [.vector 1 xs, .integer xs.length] =
      some (.words32 (widen32 kind xs)) := by
  cases kind <;> simp [extendByte32Prim, intrinsic, reductionIntrinsic, hx]

theorem add_tu_intrinsic (cfg : Config) (m : Memory) (acc active : List (BitVec 32))
    (ha : acc.length = cfg.capacity) (hx : active.length ≤ cfg.capacity) :
    intrinsic cfg m .addI32TURVV [.words32 acc, .words32 acc, .words32 active, .integer active.length] =
      some (.words32 (addPrefix acc active)) := by
  simp [intrinsic, reductionIntrinsic, ha, hx, addPrefix]

theorem rvv_reduce_intrinsic (cfg : Config) (m : Memory) (xs : List (BitVec 32))
    (seed : List (BitVec 32)) (hx : xs.length = cfg.capacity) (hcap : 0 < cfg.capacity)
    (hs : 0 < seed.length) (hsmax : seed.length ≤ cfg.capacity / 8) :
    intrinsic cfg m .reduceI32RVV [.words32 xs, .words32 seed, .integer cfg.capacity] =
      some (.words32 [seed.head! + sumWords xs]) := by
  simp [intrinsic, reductionIntrinsic, hx, hcap, hs, hsmax, List.take_of_length_le (show xs.length ≤ cfg.capacity by omega)]

theorem scalar32_intrinsic (cfg : Config) (m : Memory) (kind : Interpretation) (x : BitVec 32) :
    intrinsic cfg m (scalar32Prim kind) [.words32 [x]] = some (.integer (value kind x)) := by
  cases kind <;> simp [scalar32Prim, intrinsic, reductionIntrinsic] <;> rfl

/-- The intrinsic has no destination passthrough. At vl=0 it supplies no
specified scalar result, so the supported fragment rejects that case. -/
theorem zero_vl_reduction_rejected (cfg : Config) (m : Memory)
    (xs seed : List (BitVec 32)) :
    intrinsic cfg m .reduceI32RVV [.words32 xs, .words32 seed, .integer 0] = none := by
  simp [intrinsic, reductionIntrinsic]

end Salty.CByte
