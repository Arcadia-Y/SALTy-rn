import Salty.Spec.X32Pack
import Salty.Proofs.X32Pack.NeonSingle

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Salty.Kernels.X32Pack
open CByte

/-- These are projections of the independently extracted source and target,
including the source's different ordering of the bias increment and store. -/
def pairHeader (rvv : Bool) : Stmt :=
  firstStatement (if rvv then rvvChannelBody else neonChannelBody)
def oddHeader (rvv : Bool) : Stmt :=
  takeStatements 2 (if rvv then rvvOdd else neonOdd)

def headerBytes (m : Memory) (bias : Address) (paired : Bool) : List Byte :=
  if bias = 0 then List.replicate 8 0 else readBytes m bias (if paired then 8 else 4)

structure HeaderLocals (s : State) (bias output : Address) : Prop where
  bias : s.locals "bias" = some (.pointer bias)
  output : s.locals "packed_weights" = some (.pointer output)

structure HeaderSafe (m : Memory) (bias output : Address) (paired : Bool) : Prop where
  readable : bias ≠ 0 → ∀ p, Footprint bias (if paired then 8 else 4) p → m.readable p = true
  writable : ∀ p, Footprint output 8 p → m.writable p = true

private theorem update_memory (s : State) (name : String) (v : Value) :
    (update s name v).memory = s.memory := rfl
private theorem update_locals (s : State) (name key : String) (v : Value) :
    (update s name v).locals key = if key = name then some v else s.locals key := rfl

def pairHeaderAfter (rvv : Bool) (s : State) (bias output : Address) : State :=
  let bs := headerBytes s.memory bias true
  let t := update s (if bias = 0 then "vzero" else "vb0") (.vector 4 bs)
  let t := if bias = 0 then t else update t "bias" (.pointer (bias+8))
  let t := { t with memory := writeBytes s.memory output bs }
  -- Both store/increment orders have the same local environment and memory.
  let _ := rvv
  update t "packed_weights" (.pointer (output+8))

theorem pair_header_shape (rvv : Bool) : pairHeader rvv =
  .branch (.bin .ne (.var "bias") .null)
    (if rvv then
      .seq (.assign "vb0" (.call .loadU32PackM1 [.var "bias", .cast .u64 (.lit 2)]))
      (.seq (.effect .storeU32RVV [.var "packed_weights", .var "vb0", .cast .u64 (.lit 2)])
      (.seq (.assign "bias" (.offset 4 (.var "bias") (.lit 2)))
      (.seq (.assign "packed_weights" (.offset 4 (.var "packed_weights") (.lit 2))) .skip)))
    else
      .seq (.assign "vb0" (.call .loadU32x2 [.var "bias"]))
      (.seq (.assign "bias" (.offset 4 (.var "bias") (.lit 2)))
      (.seq (.effect .storeU32x2 [.var "packed_weights", .var "vb0"])
      (.seq (.assign "packed_weights" (.offset 4 (.var "packed_weights") (.lit 2))) .skip))))
    (if rvv then
      .seq (.assign "vzero" (.call .dupU32PackM1 [.cast .u32 (.lit 0), .cast .u64 (.lit 2)]))
      (.seq (.effect .storeU32RVV [.var "packed_weights", .var "vzero", .cast .u64 (.lit 2)])
      (.seq (.assign "packed_weights" (.offset 4 (.var "packed_weights") (.lit 2))) .skip))
    else
      .seq (.assign "vzero" (.call .dupU32x2 [.cast .u32 (.lit 0)]))
      (.seq (.effect .storeU32x2 [.var "packed_weights", .var "vzero"])
      (.seq (.assign "packed_weights" (.offset 4 (.var "packed_weights") (.lit 2))) .skip))) := by
  cases rvv <;> rfl

theorem header_zero_neon (cfg : Config) (m : Memory) :
    intrinsic cfg m .dupU32x2 [.integer 0] = some (.vector 4 (List.replicate 8 0)) := rfl

theorem header_zero_rvv (cfg : Config) (m : Memory) (cap : 2 ≤ cfg.capacity / 4) :
    intrinsic cfg m .dupU32PackM1 [.integer 0, .integer 2] =
      some (.vector 4 (List.replicate 8 0)) := by
  simp [intrinsic, tupleMemoryIntrinsic, cap, bytes32]

theorem header_store_neon (m : Memory) (output : Address) (bs : List Byte)
    (len : bs.length = 8) (safe : ∀ p, Footprint output 8 p → m.writable p = true) :
    effect m .storeU32x2 [.pointer output, .vector 4 bs] = some (writeBytes m output bs) := by
  simpa [effect, storeVector, len] using storeBytes_success m output bs (by simpa [len] using safe)

theorem header_store_rvv (m : Memory) (output : Address) (bs : List Byte)
    (len : bs.length = 8) (safe : ∀ p, Footprint output 8 p → m.writable p = true) :
    effect m .storeU32RVV [.pointer output, .vector 4 bs, .integer 2] = some (writeBytes m output bs) := by
  have take : bs.take 8 = bs := List.take_of_length_le (by omega)
  simpa [effect, len, take] using storeBytes_success m output bs (by simpa [len] using safe)

theorem pair_header_exec (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (s : State) (bias output : Address) (loc : HeaderLocals s bias output)
    (safe : HeaderSafe s.memory bias output true) :
    Exec cfg (pairHeader rvv) s (pairHeaderAfter rvv s bias output) := by
  have cap : 2 ≤ cfg.capacity / 4 := by omega
  rw [pair_header_shape]
  by_cases zero : bias = 0#64
  · subst bias
    have storeN := header_store_neon s.memory output (List.replicate 8 0) (by simp) safe.writable
    have storeR := header_store_rvv s.memory output (List.replicate 8 0) (by simp) safe.writable
    simp at storeN storeR
    apply Exec.no (v := .integer 0)
    · simp [eval, binary, loc.bias]
    · rfl
    apply run_sound (fuel := 12)
    cases rvv <;>
      simp [run, eval, binary, convert, update_memory, update_locals, loc.bias, loc.output,
        header_zero_neon, header_zero_rvv cfg s.memory cap, storeN, storeR,
        pairHeaderAfter, headerBytes, show max (2 : Int) 0 = 2 by decide]
    all_goals rfl
  · have load := loadBytes_success s.memory bias 8 (safe.readable zero)
    have loadN : intrinsic cfg s.memory .loadU32x2 [.pointer bias] =
        some (.vector 4 (readBytes s.memory bias 8)) := by simp [intrinsic, load]
    have loadR : intrinsic cfg s.memory .loadU32PackM1 [.pointer bias, .integer 2] =
        some (.vector 4 (readBytes s.memory bias 8)) := by simp [intrinsic, tupleMemoryIntrinsic, cap, load]
    have storeN := header_store_neon s.memory output (readBytes s.memory bias 8) (by simp) safe.writable
    have storeR := header_store_rvv s.memory output (readBytes s.memory bias 8) (by simp) safe.writable
    apply Exec.yes (v := .integer 1)
    · simp [eval, binary, loc.bias, zero]
    · rfl
    apply run_sound (fuel := 14)
    cases rvv <;>
      simp [run, eval, binary, convert, update_memory, update_locals, loc.bias, loc.output,
        loadN, loadR, storeN, storeR, pairHeaderAfter, headerBytes, zero,
        show max (2 : Int) 0 = 2 by decide]
    all_goals rfl

theorem pairHeaderAfter_memory (rvv : Bool) (s : State) (bias output : Address) :
    (pairHeaderAfter rvv s bias output).memory = writeBytes s.memory output (headerBytes s.memory bias true) := by
  simp [pairHeaderAfter, update_memory]

theorem pairHeaderAfter_locals (rvv : Bool) (s : State) (bias output : Address)
    (loc : HeaderLocals s bias output) :
    HeaderLocals (pairHeaderAfter rvv s bias output) (nextBias bias true) (output+8) := by
  constructor <;> by_cases h : bias = 0#64 <;>
    simp [pairHeaderAfter, nextBias, h, update_locals, loc.bias]

def oddHeaderBranch (rvv : Bool) : Stmt := firstStatement (if rvv then rvvOdd else neonOdd)

def oddHeaderWritten (s : State) (bias output : Address) : State :=
  let bs := headerBytes s.memory bias false
  let t := if bias = 0 then update s "vzero_2" (.vector 4 bs) else s
  let t := { t with memory := writeBytes s.memory output bs }
  if bias = 0 then t else update t "bias" (.pointer (bias+4))

def oddHeaderAfter (s : State) (bias output : Address) : State :=
  update (oddHeaderWritten s bias output) "packed_weights" (.pointer (output+8))

theorem odd_header_shape (rvv : Bool) : oddHeader rvv =
    .seq (oddHeaderBranch rvv)
      (.seq (.assign "packed_weights" (.offset 4 (.var "packed_weights") (.lit 2))) .skip) := by
  cases rvv <;> rfl

theorem odd_header_branch_shape (rvv : Bool) : oddHeaderBranch rvv =
  .branch (.bin .ne (.var "bias") .null)
    (.seq (.seq (.effect .storeU32 [.var "packed_weights", .cast .u32 (.param (.var "bias") 0)])
      (.assign "bias" (.offset 4 (.var "bias") (.lit 1)))) .skip)
    (if rvv then
      .seq (.assign "vzero_2" (.call .dupU32PackM1 [.cast .u32 (.lit 0), .cast .u64 (.lit 2)]))
      (.seq (.effect .storeU32RVV [.var "packed_weights", .var "vzero_2", .cast .u64 (.lit 2)]) .skip)
    else
      .seq (.assign "vzero_2" (.call .dupU32x2 [.cast .u32 (.lit 0)]))
      (.seq (.effect .storeU32x2 [.offset 4 (.var "packed_weights") (.lit 0), .var "vzero_2"]) .skip)) := by
  cases rvv <;> rfl

theorem odd_header_branch_exec (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (s : State) (bias output : Address) (loc : HeaderLocals s bias output)
    (safe : HeaderSafe s.memory bias output false) :
    Exec cfg (oddHeaderBranch rvv) s (oddHeaderWritten s bias output) := by
  rw [odd_header_branch_shape]
  by_cases zero : bias = 0#64
  · subst bias
    have cap : 2 ≤ cfg.capacity / 4 := by omega
    have storeN := header_store_neon s.memory output (List.replicate 8 0) (by simp) safe.writable
    have storeR := header_store_rvv s.memory output (List.replicate 8 0) (by simp) safe.writable
    simp at storeN storeR
    apply Exec.no (v := .integer 0)
    · simp [eval, binary, loc.bias]
    · rfl
    apply run_sound (fuel := 8)
    cases rvv <;>
      simp [run, eval, convert, update_memory, update_locals, loc.output,
        header_zero_neon, header_zero_rvv cfg s.memory cap, storeN, storeR,
        oddHeaderWritten, headerBytes, show max (2 : Int) 0 = 2 by decide]
  · obtain ⟨value, load, bytes, lo, hi⟩ := unsigned_load_roundtrip s.memory bias (safe.readable zero)
    have store : effect s.memory .storeU32 [.pointer output, .integer (convert .u32 value)] =
        some (writeBytes s.memory output (readBytes s.memory bias 4)) := by
      have raw := storeBytes_success s.memory output (readBytes s.memory bias 4)
        (fun p hp => safe.writable p (footprint_mono (by simp) hp))
      have upper : convert .u32 value < 4294967296 := hi
      simpa [effect, lo, upper, bytes] using raw
    let written : State := { s with memory := writeBytes s.memory output (readBytes s.memory bias 4) }
    have copy : Exec cfg (.effect .storeU32 [.var "packed_weights", .cast .u32 (.param (.var "bias") 0)]) s written := by
      apply Exec.effect (vs := [.pointer output, .integer (convert .u32 value)])
      · simp [eval, loc.output, loc.bias, load]
      · exact store
    have biasStep : Exec cfg (.assign "bias" (.offset 4 (.var "bias") (.lit 1))) written
        (update written "bias" (.pointer (bias+4))) := by
      apply Exec.assign
      simp [eval, written, loc.bias]
    apply Exec.yes (v := .integer 1)
    · simp [eval, binary, loc.bias, zero]
    · rfl
    simpa [oddHeaderWritten, headerBytes, zero, written] using Exec.seq (Exec.seq copy biasStep) Exec.skip

theorem odd_header_exec (rvv : Bool) (cfg : Config) (capacity : 8 ≤ cfg.capacity)
    (s : State) (bias output : Address) (loc : HeaderLocals s bias output)
    (safe : HeaderSafe s.memory bias output false) :
    Exec cfg (oddHeader rvv) s (oddHeaderAfter s bias output) := by
  have branch := odd_header_branch_exec rvv cfg capacity s bias output loc safe
  have outputLoc : (oddHeaderWritten s bias output).locals "packed_weights" = some (.pointer output) := by
    by_cases zero : bias = 0#64 <;> simp [oddHeaderWritten, zero, update_locals, loc.output]
  rw [odd_header_shape]
  refine .seq branch (.seq ?_ .skip)
  apply Exec.assign
  simp [eval, outputLoc]

theorem oddHeaderAfter_memory (s : State) (bias output : Address) :
    (oddHeaderAfter s bias output).memory = writeBytes s.memory output (headerBytes s.memory bias false) := by
  by_cases zero : bias = 0#64 <;> simp [oddHeaderAfter, oddHeaderWritten, update_memory, zero]

theorem oddHeaderAfter_locals (s : State) (bias output : Address) (loc : HeaderLocals s bias output) :
    HeaderLocals (oddHeaderAfter s bias output) (nextBias bias false) (output+8) := by
  constructor <;> by_cases h : bias = 0#64 <;>
    simp [oddHeaderAfter, oddHeaderWritten, nextBias, h, update_locals, loc.bias]

end Salty.Kernels.X32Pack
