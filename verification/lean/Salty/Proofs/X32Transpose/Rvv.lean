import Salty.Spec.X32Transpose
import Salty.Proofs.X32Transpose.Columns

namespace Salty.Kernels.X32Transpose
open CByte

def rvvInit : Stmt := takeStatements 5 Generated.X32Transpose.rvv

def widthInitialized (s : State) (p : MatrixCopy) : State :=
  let t := update s "bw" (.integer p.cols)
  if p.cols = 0 then update t "bw" (.integer 1) else t

def rvvInitialized (s : State) (p : MatrixCopy) : State :=
  let t := widthInitialized s p
  if p.rows = 0 then update t "bw" (.integer 0) else t

theorem geometry_assert (cfg : Config) (s : State) (x y stride : String)
    (a b k : Nat) (ha : s.locals x = some (.integer a))
    (hb : s.locals y = some (.integer b)) (hk : s.locals stride = some (.integer k))
    (geometry : a = 1 ∨ convert .u64 ((b : Int)*4) ≤ k) :
    Exec cfg (.effect .assertion [(.not (.not (.or
      (.bin .eq (.var x) (.cast .u64 (.lit 1)))
      (.bin .ge (.var stride) (.cast .u64 (.bin .mul (.var y) (.lit 4)))))))]) s s := by
  have he : eval cfg s (.or (.bin .eq (.var x) (.cast .u64 (.lit 1)))
      (.bin .ge (.var stride) (.cast .u64 (.bin .mul (.var y) (.lit 4))))) = some (.integer 1) := by
    by_cases one : a = 1
    · simp [eval, binary, ha, one, truth, show convert .u64 1 = 1 by decide]
    · have bound : convert .u64 ((b : Int)*4) ≤ k := geometry.resolve_left one
      simp [eval, binary, ha, hb, hk, truth, one,
        show convert .u64 1 = 1 by decide, Int.natCast_mul, bound]
  apply Exec.effect (vs := [.integer 1])
  · simp [List.mapM_cons, eval, he, truth]
  · rfl

private theorem zero_assign (cfg : Config) (s : State) (name : String) (n value : Nat)
    (h : s.locals name = some (.integer n)) (bound : value < 2^64) :
    Exec cfg (.branch (.bin .eq (.var name) (.cast .u64 (.lit 0)))
      (.seq (.assign "bw" (.cast .u64 (.lit value))) .skip) .skip)
      s (if n = 0 then update s "bw" (.integer value) else s) := by
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte]
    apply Exec.yes (v := .integer 1)
    · simp [eval, binary, h, hn, show convert .u64 0 = 0 by decide]
    · rfl
    · exact .seq (.assign (by simp [eval, cast_nat value bound])) .skip
  · simp only [hn, ↓reduceIte]
    apply Exec.no (v := .integer 0)
    · simp [eval, binary, h, hn, show convert .u64 0 = 0 by decide]
    · rfl
    · exact .skip

theorem rvv_init_exec (cfg : Config) (s : State) (p : MatrixCopy) (h : Arguments s p)
    (outStride : p.cols = 1 ∨ convert .u64 ((p.rows : Int)*4) ≤ p.outputStride)
    (inStride : p.rows = 1 ∨ convert .u64 ((p.cols : Int)*4) ≤ p.inputStride) :
    Exec cfg rvvInit s (rvvInitialized s p) := by
  have ho := geometry_assert cfg s "block_width" "block_height" "output_stride"
    p.cols p.rows p.outputStride h.width h.height h.outputStride outStride
  have hi := geometry_assert cfg s "block_height" "block_width" "input_stride"
    p.rows p.cols p.inputStride h.height h.width h.inputStride inStride
  have hw := zero_assign cfg (update s "bw" (.integer p.cols)) "bw" p.cols 1
    (by simp [update]) (by decide)
  have hh := zero_assign cfg (widthInitialized s p) "block_height" p.rows 0
    (by unfold widthInitialized; split <;> simp [update, h.height]) (by decide)
  exact .seq ho (.seq hi (.seq (.assign (by simpa [eval] using h.width)) (.seq hw (.seq hh .skip))))

@[simp] theorem rvv_initialized_memory (s : State) (p : MatrixCopy) :
    (rvvInitialized s p).memory = s.memory := by
  unfold rvvInitialized widthInitialized
  split <;> split <;> rfl

theorem rvv_initialized_locals (s : State) (p : MatrixCopy) (h : Arguments s p) :
    ColumnLocals (rvvInitialized s p) (effectiveMatrix p) := by
  by_cases hz : p.rows = 0 <;> by_cases wz : p.cols = 0 <;>
    constructor <;> simp [rvvInitialized, widthInitialized, effectiveMatrix, update,
      hz, wz, h.height, h.inputPtr, h.outputPtr, h.inputStride, h.outputStride]

/-- Complete extracted RVV function, including assertions and zero dimensions.
These are intrinsic-model premises; a common source/target C caller contract
must additionally cover object bounds, padding, alignment, and ABI validity. -/
theorem rvv_function_total (cfg : Config) (s : State) (p : MatrixCopy)
    (h : Arguments s p) (heightBound : p.rows < 2^64) (widthBound : p.cols < 2^64)
    (outStride : p.cols = 1 ∨ convert .u64 ((p.rows : Int)*4) ≤ p.outputStride)
    (inStride : p.rows = 1 ∨ convert .u64 ((p.cols : Int)*4) ≤ p.inputStride)
    (safe : RowsSafe s.memory p.input p.output p.inputStride p.outputStride p.rows (effectiveMatrix p).cols)
    (sep : (effectiveMatrix p).separated) :
    ∃ t, Exec cfg Generated.X32Transpose.rvv s t ∧ t.memory = (effectiveMatrix p).result s.memory := by
  have colsBound : (effectiveMatrix p).cols < 2^64 := by
    simp only [effectiveMatrix]
    split <;> try omega
    split <;> omega
  obtain ⟨t, ht, hm⟩ := rvv_columns_total cfg (rvvInitialized s p) (effectiveMatrix p)
    (rvv_initialized_locals s p h) (by change p.rows < 2^64; omega) colsBound
    (by simpa only [rvv_initialized_memory] using safe) sep
  exact ⟨t, exec_take_drop 5 (rvv_init_exec cfg s p h outStride inStride)
    (.seq ht .skip), by simpa only [rvv_initialized_memory] using hm⟩

end Salty.Kernels.X32Transpose
