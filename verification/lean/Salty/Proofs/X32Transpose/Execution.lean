import Salty.Spec.X32Transpose
import Salty.Proofs.Core.CByteSyntax
import Salty.Proofs.Core.CWordMemory
import Salty.Generated.X32TransposeNeon
import Salty.Generated.X32TransposeRvv

/-! Exact blocks of the independently extracted transpose programs.
These are supporting proofs; no whole transpose equivalence is claimed yet. -/
namespace Salty.Kernels.X32Transpose
open CByte

def rvvColumns : Stmt := firstStatement (dropStatements 5 Generated.X32Transpose.rvv)
def rvvRows : Stmt := firstStatement (dropStatements 4 (loopBody rvvColumns))
def rvvRowBody : Stmt := loopBody rvvRows

structure RowLocals (s : State) (n vl : Nat) (input output : Address)
    (inputStride outputStride : Nat) : Prop where
  height : s.locals "bh" = some (.integer n)
  lanes : s.locals "vl" = some (.integer vl)
  inputPtr : s.locals "i" = some (.pointer input)
  outputPtr : s.locals "o" = some (.pointer output)
  inputStride : s.locals "input_stride" = some (.integer inputStride)
  outputStride : s.locals "output_stride" = some (.integer outputStride)

def rowAfter (s : State) (n : Nat) (input output : Address) (inputStride : Nat)
    (bs : List Byte) (m : Memory) : State :=
  let t := update s "v" (.vector 4 bs)
  let t := {t with memory := m}
  let t := update t "i" (.pointer (input + BitVec.ofNat 64 inputStride))
  let t := update t "o" (.pointer (output + 4#64))
  update t "bh" (.integer (n - 1 : Nat))

theorem cast_u64_word (n : Int) : BitVec.ofInt 64 (convert .u64 n) = BitVec.ofInt 64 n := by
  change BitVec.ofInt 64 ((BitVec.ofInt 64 n).toNat : Int) = BitVec.ofInt 64 n
  simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cast_i64_word (n : Int) : BitVec.ofInt 64 (convert .i64 n) = BitVec.ofInt 64 n := by
  simp only [convert, BitVec.ofInt_toInt]

theorem pointer_integer_add (a : Address) (n : Int) :
    BitVec.ofInt 64 (convert .u64 ((a.toNat : Int) + n)) = a + BitVec.ofInt 64 n := by
  rw [cast_u64_word, BitVec.ofInt_add]
  simp

theorem rvv_row_exec (cfg : Config) (s : State) (n vl : Nat) (input output : Address)
    (inputStride outputStride : Nat) (bs : List Byte) (m : Memory)
    (locals : RowLocals s n vl input output inputStride outputStride)
    (positive : 0 < n) (bound : n < 2^64) (capacity : vl ≤ cfg.capacity)
    (length : bs.length = 4 * vl)
    (layout : DisjointStride32 (BitVec.ofNat 64 outputStride) vl)
    (hload : loadBytes s.memory input (4 * vl) = some bs)
    (hstore : storeStrided32 s.memory output (BitVec.ofNat 64 outputStride) bs vl = some m) :
    Exec cfg rvvRowBody s (rowAfter s n input output inputStride bs m) := by
  have hc : convert .u64 ((n : Int) - 1) = (n - 1 : Nat) :=
    cast_sub n 1 positive bound
  have hone : convert .u64 1 = 1 := by decide
  apply run_sound (fuel := 16)
  simp [rvvRowBody, rvvRows, rvvColumns, firstStatement, dropStatements, loopBody,
    Generated.X32Transpose.rvv, run, eval, intrinsic, effect, update,
    locals.height, locals.lanes, locals.inputPtr, locals.outputPtr,
    locals.inputStride, locals.outputStride, capacity, length, layout, hload, hstore,
    binary, cast_i64_word, pointer_integer_add, rowAfter, hc, hone]

theorem rowAfter_locals (s : State) (n vl : Nat) (input output : Address)
    (inputStride outputStride : Nat) (bs : List Byte) (m : Memory)
    (h : RowLocals s n vl input output inputStride outputStride) :
    RowLocals (rowAfter s n input output inputStride bs m) (n - 1) vl
      (input + BitVec.ofNat 64 inputStride) (output + 4#64) inputStride outputStride := by
  constructor <;> simp [rowAfter, update, h.height, h.lanes, h.inputPtr, h.outputPtr,
    h.inputStride, h.outputStride]

theorem rowAddress_succ (a : Address) (stride row : Nat) :
    rowAddress a stride (row + 1) = rowAddress (a + BitVec.ofNat 64 stride) stride row := by
  simp only [rowAddress, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
  ac_rfl

structure RowsSafe (m : Memory) (input output : Address)
    (inputStride outputStride rows lanes : Nat) : Prop where
  layout : 0 < rows → DisjointStride32 (BitVec.ofNat 64 outputStride) lanes
  readable : ∀ r, r < rows → ∀ p, Footprint (rowAddress input inputStride r) (4 * lanes) p →
    m.readable p = true
  writable : ∀ r, r < rows → ∀ p,
    StridedFootprint (rowAddress output 4 r) (BitVec.ofNat 64 outputStride) lanes p →
    m.writable p = true
  separate : ∀ r, r < rows → ∀ w, w < rows → ∀ p,
    Footprint (rowAddress input inputStride r) (4 * lanes) p →
    ¬ StridedFootprint (rowAddress output 4 w) (BitVec.ofNat 64 outputStride) lanes p

theorem RowsSafe.advance {m : Memory} {input output : Address}
    {inputStride outputStride rows lanes : Nat}
    (h : RowsSafe m input output inputStride outputStride (rows + 1) lanes) (bs : List Byte) :
    RowsSafe (writeStrided32 m output (BitVec.ofNat 64 outputStride) bs lanes)
      (input + BitVec.ofNat 64 inputStride) (output + 4#64) inputStride outputStride rows lanes := by
  constructor
  · intro positive
    exact h.layout (by omega)
  · intro r hr p hp
    rw [writeStrided32_readable]
    exact h.readable (r + 1) (by omega) p (by simpa only [rowAddress_succ] using hp)
  · intro r hr p hp
    rw [writeStrided32_writable]
    exact h.writable (r + 1) (by omega) p (by simpa only [rowAddress_succ] using hp)
  · intro r hr w hw p hp
    have hs := h.separate (r + 1) (by omega) (w + 1) (by omega) p
    simpa only [rowAddress_succ] using hs (by simpa only [rowAddress_succ] using hp)

/-- Functional effect of a sequence of row loads followed by strided stores.
This intermediate result still follows RVV row order; proving it equals the
common matrix transpose is a separate obligation. -/
def rowsResult (m : Memory) (input output : Address)
    (inputStride outputStride lanes : Nat) : Nat → Memory
  | 0 => m
  | rows + 1 => rowsResult
      (writeStrided32 m output (BitVec.ofNat 64 outputStride)
        (readBytes m input (4 * lanes)) lanes)
      (input + BitVec.ofNat 64 inputStride) (output + 4#64)
      inputStride outputStride lanes rows

theorem rvv_rows_total (cfg : Config) (s : State) (rows lanes : Nat) (input output : Address)
    (inputStride outputStride : Nat)
    (locals : RowLocals s rows lanes input output inputStride outputStride)
    (bound : rows < 2^64) (capacity : lanes ≤ cfg.capacity)
    (safe : RowsSafe s.memory input output inputStride outputStride rows lanes) :
    ∃ t, Exec cfg rvvRows s t ∧
      t.memory = rowsResult s.memory input output inputStride outputStride lanes rows := by
  induction rows generalizing s input output with
  | zero =>
    refine ⟨s, ?_, rfl⟩
    apply Exec.done (v := .integer 0)
    · simp [rvvRows, rvvColumns, firstStatement, dropStatements, loopBody,
        Generated.X32Transpose.rvv, eval, binary, locals.height, convert]
    · rfl
  | succ rows ih =>
    let bs := readBytes s.memory input (4 * lanes)
    let m := writeStrided32 s.memory output (BitVec.ofNat 64 outputStride) bs lanes
    have hl : loadBytes s.memory input (4 * lanes) = some bs := by
      apply loadBytes_success
      intro p hp
      exact safe.readable 0 (by omega) p (by simpa [rowAddress] using hp)
    have hs : storeStrided32 s.memory output (BitVec.ofNat 64 outputStride) bs lanes = some m := by
      apply storeStrided32_success
      · simp [bs, readBytes_length]
      · intro p hp
        exact safe.writable 0 (by omega) p (by simpa [rowAddress] using hp)
    let t := rowAfter s (rows + 1) input output inputStride bs m
    have he : Exec cfg rvvRowBody s t := rvv_row_exec cfg s (rows + 1) lanes input output
      inputStride outputStride bs m locals (by omega) bound capacity (by simp [bs]) (safe.layout (by omega)) hl hs
    have ht : RowLocals t rows lanes (input + BitVec.ofNat 64 inputStride) (output + 4#64)
        inputStride outputStride := by
      simpa only [Nat.add_sub_cancel] using rowAfter_locals s (rows + 1) lanes input output
        inputStride outputStride bs m locals
    obtain ⟨u, hu, hm⟩ := ih t _ _ ht (by omega) (safe.advance bs)
    refine ⟨u, ?_, hm⟩
    apply Exec.more (v := .integer 1) (t := t)
    · simp [rvvRows, rvvColumns, firstStatement, dropStatements, loopBody,
        Generated.X32Transpose.rvv, eval, binary, locals.height, convert, Int.max_def]
    · rfl
    · exact he
    · exact hu

def neonOuter : Stmt := firstStatement (dropStatements 13 Generated.X32Transpose.neon)
def neonOuterBody : Stmt := firstStatement neonOuter
def neonRows : Stmt := firstStatement (dropStatements 2 neonOuterBody)
def neonRowBody : Stmt := loopBody neonRows

structure NeonRowLocals (s : State) (n offset : Nat) (i0 i1 o0 o1 : Address) : Prop where
  height : s.locals "bh" = some (.integer n)
  input0 : s.locals "i0" = some (.pointer i0)
  input1 : s.locals "i1" = some (.pointer i1)
  output0 : s.locals "o0" = some (.pointer o0)
  output1 : s.locals "o1" = some (.pointer o1)
  inputOffset : s.locals "input_offset" = some (.integer offset)
  outputOffset : s.locals "tile_hbytes" = some (.integer 8)

def neonRowAfter (s : State) (n offset : Nat) (i0 i1 o0 o1 : Address)
    (a b c d : List Byte) (m1 m2 : Memory) : State :=
  let t := update s "v1_0" (.vector 4 (a ++ b))
  let t := update t "i0" (.pointer (i0 + BitVec.ofNat 64 offset))
  let t := update t "v1_1" (.vector 4 (c ++ d))
  let t := update t "i1" (.pointer (i1 + BitVec.ofNat 64 offset))
  let t := update t "v0_0" (.vectors 4 [a ++ c, b ++ d])
  let t := {t with memory := m1}
  let t := update t "o1" (.pointer (o1 + 8#64))
  let t := {t with memory := m2}
  let t := update t "o0" (.pointer (o0 + 8#64))
  update t "bh" (.integer (n - 2 : Nat))

/-- The extracted 2x2 source tile stores column 1 before column 0. Keeping the
intermediate memory is essential when the odd-width path aliases o1 with o0. -/
theorem neon_row_exec (cfg : Config) (s : State) (n offset : Nat) (i0 i1 o0 o1 : Address)
    (a b c d : List Byte) (m1 m2 : Memory)
    (locals : NeonRowLocals s n offset i0 i1 o0 o1)
    (height : 2 ≤ n) (bound : n < 2^64)
    (ha : a.length = 4) (hb : b.length = 4) (hc : c.length = 4) (hd : d.length = 4)
    (load0 : loadBytes s.memory i0 8 = some (a ++ b))
    (load1 : loadBytes s.memory i1 8 = some (c ++ d))
    (store1 : storeBytes s.memory o1 (b ++ d) = some m1)
    (store0 : storeBytes m1 o0 (a ++ c) = some m2) :
    Exec cfg neonRowBody s (neonRowAfter s n offset i0 i1 o0 o1 a b c d m1 m2) := by
  have hn : convert .u64 ((n : Int) - 2) = (n - 2 : Nat) := cast_sub n 2 height bound
  have htwo : convert .u64 2 = 2 := by decide
  have hzip := zipU32x2_blocks cfg s.memory a b c d ha hb hc hd
  apply run_sound (fuel := 24)
  simp [neonRowBody, neonRows, neonOuterBody, neonOuter, firstStatement,
    dropStatements, loopBody, Generated.X32Transpose.neon, run, eval,
    locals.height, locals.input0, locals.input1, locals.output0, locals.output1,
    locals.inputOffset, locals.outputOffset, update, binary, pointer_integer_add,
    load0, load1, store0, store1, hzip, intrinsic, effect, storeVector,
    ha, hb, hc, hd, List.take_left' ha, List.take_left' hc, List.drop_left' ha,
    List.drop_left' hc, neonRowAfter, hn, htwo]

/-- At odd final width (including zero), the source aliases its output columns.
Its second store erases the entire first store, leaving exactly column zero. -/
theorem neon_row_alias_result (cfg : Config) (s : State) (n offset : Nat)
    (i0 i1 output : Address) (a b c d : List Byte)
    (locals : NeonRowLocals s n offset i0 i1 output output)
    (height : 2 ≤ n) (bound : n < 2^64)
    (ha : a.length = 4) (hb : b.length = 4) (hc : c.length = 4) (hd : d.length = 4)
    (load0 : loadBytes s.memory i0 8 = some (a ++ b))
    (load1 : loadBytes s.memory i1 8 = some (c ++ d))
    (safe : ∀ p, Footprint output 8 p → s.memory.writable p = true) :
    ∃ t, Exec cfg neonRowBody s t ∧ t.memory = writeBytes s.memory output (a ++ c) := by
  let m1 := writeBytes s.memory output (b ++ d)
  let m2 := writeBytes m1 output (a ++ c)
  have hs1 : storeBytes s.memory output (b ++ d) = some m1 := by
    apply storeBytes_success
    simpa only [List.length_append, hb, hd] using safe
  have hs2 : storeBytes m1 output (a ++ c) = some m2 := by
    apply storeBytes_success
    simpa only [m1, writeBytes_writable, List.length_append, ha, hc] using safe
  refine ⟨neonRowAfter s n offset i0 i1 output output a b c d m1 m2,
    neon_row_exec cfg s n offset i0 i1 output output a b c d m1 m2 locals height bound
      ha hb hc hd load0 load1 hs1 hs2, ?_⟩
  change writeBytes (writeBytes s.memory output (b ++ d)) output (a ++ c) = _
  apply writeBytes_overwrite
  simp [ha, hb, hc, hd]

/-- Row-wise transpose writes with every lane read from the original memory.
This is a refinement specification, not an executable source replacement. -/
def rowsWrite (original working : Memory) (input output : Address)
    (inputStride outputStride lanes : Nat) : Nat → Memory
  | 0 => working
  | rows + 1 => rowsWrite original
      (writeStrided32 working output (BitVec.ofNat 64 outputStride)
        (readBytes original input (4 * lanes)) lanes)
      (input + BitVec.ofNat 64 inputStride) (output + 4#64)
      inputStride outputStride lanes rows

theorem rowsResult_original (original working : Memory) (input output : Address)
    (inputStride outputStride lanes rows : Nat)
    (safe : RowsSafe working input output inputStride outputStride rows lanes)
    (agree : ∀ r, r < rows →
      readBytes working (rowAddress input inputStride r) (4 * lanes) =
      readBytes original (rowAddress input inputStride r) (4 * lanes)) :
    rowsResult working input output inputStride outputStride lanes rows =
      rowsWrite original working input output inputStride outputStride lanes rows := by
  induction rows generalizing working input output with
  | zero => rfl
  | succ rows ih =>
    have head : readBytes working input (4 * lanes) = readBytes original input (4 * lanes) := by
      simpa [rowAddress] using agree 0 (by omega)
    simp only [rowsResult, rowsWrite, head]
    apply ih
    · exact safe.advance _
    · intro r hr
      rw [readBytes_writeStrided32_disjoint]
      · simpa only [rowAddress_succ] using agree (r + 1) (by omega)
      · intro address hread
        have hs := safe.separate (r + 1) (by omega) 0 (by omega) address
        simpa [rowAddress] using hs (by simpa only [rowAddress_succ] using hread)

theorem rvv_rows_original (cfg : Config) (s : State) (rows lanes : Nat) (input output : Address)
    (inputStride outputStride : Nat)
    (locals : RowLocals s rows lanes input output inputStride outputStride)
    (bound : rows < 2^64) (capacity : lanes ≤ cfg.capacity)
    (safe : RowsSafe s.memory input output inputStride outputStride rows lanes) :
    ∃ t, Exec cfg rvvRows s t ∧
      t.memory = rowsWrite s.memory s.memory input output inputStride outputStride lanes rows := by
  obtain ⟨t, ht, hm⟩ := rvv_rows_total cfg s rows lanes input output inputStride outputStride
    locals bound capacity safe
  refine ⟨t, ht, hm.trans ?_⟩
  exact rowsResult_original s.memory s.memory input output inputStride outputStride lanes rows safe
    (by intro r hr; rfl)

end Salty.Kernels.X32Transpose
