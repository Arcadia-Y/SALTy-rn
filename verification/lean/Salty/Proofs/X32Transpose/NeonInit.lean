import Salty.Proofs.X32Transpose.NeonOuter
import Salty.Proofs.X32Transpose.Rvv

namespace Salty.Kernels.X32Transpose
open CByte

def neonInit : Stmt := takeStatements 13 Generated.X32Transpose.neon

def neonDimensions (s : State) : State :=
  let t := update s "tile_height" (.integer 2)
  let t := update t "tile_width" (.integer 2)
  let t := update t "tile_hbytes" (.integer 8)
  update t "tile_wbytes" (.integer 8)

def neonResets (s : State) (p : MatrixCopy) : State :=
  let t := update (neonDimensions s) "input_reset" (.integer (neonInputReset p))
  let t := update t "input_offset" (.integer (neonInputOffset p))
  update t "output_reset" (.integer (neonOutputReset p))

def neonInitialized (s : State) (p : MatrixCopy) : State :=
  let t := update (neonResets s p) "i0" (.pointer p.input)
  let t := update t "i1" (.pointer (p.input + BitVec.ofNat 64 p.inputStride))
  let t := update t "o0" (.pointer p.output)
  update t "o1" (.pointer (p.output + BitVec.ofNat 64 p.outputStride))

theorem neon_dimensions_exec (cfg : Config) (s : State) :
    Exec cfg (takeStatements 4 (dropStatements 2 neonInit)) s (neonDimensions s) := by
  apply run_sound (fuel := 10)
  simp [neonInit, takeStatements, dropStatements, Generated.X32Transpose.neon,
    run, eval, binary, update, neonDimensions, show convert .u64 2 = 2 by decide,
    show convert .u64 8 = 8 by decide]

theorem neon_resets_exec (cfg : Config) (s : State) (p : MatrixCopy) (h : Arguments s p) :
    Exec cfg (takeStatements 3 (dropStatements 6 neonInit)) (neonDimensions s) (neonResets s p) := by
  apply run_sound (fuel := 8)
  simp [neonInit, takeStatements, dropStatements, Generated.X32Transpose.neon,
    run, eval, binary, intrinsic, update, neonDimensions, neonResets, h.height,
    h.inputStride, h.outputStride, show convert .u64 2 = 2 by decide,
    show convert .u64 8 = 8 by decide, neonInputOffset_cast, neonInputReset, neonOutputReset,
    Int.natCast_mul, Int.natCast_ediv]

theorem neon_pointers_exec (cfg : Config) (s : State) (p : MatrixCopy) (h : Arguments s p) :
    Exec cfg (dropStatements 9 neonInit) (neonResets s p) (neonInitialized s p) := by
  let t0 := update (neonResets s p) "i0" (.pointer p.input)
  let t1 := update t0 "i1" (.pointer (p.input + BitVec.ofNat 64 p.inputStride))
  let t2 := update t1 "o0" (.pointer p.output)
  have e0 : eval cfg (neonResets s p) (.var "input") = some (.pointer p.input) := by
    simp [eval, neonResets, neonDimensions, update, h.inputPtr]
  have e1 := eval_pointer_add cfg t0 "i0" "input_stride" p.input p.inputStride
    (by simp [t0, update]) (by simp [t0, neonResets, neonDimensions, update, h.inputStride])
  simp only [BitVec.ofInt_natCast] at e1
  have e2 : eval cfg t1 (.var "output") = some (.pointer p.output) := by
    simp [eval, t1, t0, neonResets, neonDimensions, update, h.outputPtr]
  have e3 := eval_pointer_add cfg t2 "o0" "output_stride" p.output p.outputStride
    (by simp [t2, update]) (by simp [t2, t1, t0, neonResets, neonDimensions, update, h.outputStride])
  simp only [BitVec.ofInt_natCast] at e3
  exact .seq (.assign e0) (.seq (.assign e1) (.seq (.assign e2) (.seq (.assign e3) .skip)))

/-- The complete source initializer, including both assertions and unsigned
reset arithmetic. No reset or stride multiplication is assumed not to wrap. -/
theorem neon_init_exec (cfg : Config) (s : State) (p : MatrixCopy) (h : Arguments s p)
    (outStride : p.cols = 1 ∨ convert .u64 ((p.rows : Int)*4) ≤ p.outputStride)
    (inStride : p.rows = 1 ∨ convert .u64 ((p.cols : Int)*4) ≤ p.inputStride) :
    Exec cfg neonInit s (neonInitialized s p) := by
  have ho := geometry_assert cfg s "block_width" "block_height" "output_stride"
    p.cols p.rows p.outputStride h.width h.height h.outputStride outStride
  have hi := geometry_assert cfg s "block_height" "block_width" "input_stride"
    p.rows p.cols p.inputStride h.height h.width h.inputStride inStride
  apply exec_take_drop 2 (.seq ho (.seq hi .skip))
  apply exec_take_drop 4 (neon_dimensions_exec cfg s)
  apply exec_take_drop 3 (neon_resets_exec cfg s p h)
  exact neon_pointers_exec cfg s p h

@[simp] theorem neon_initialized_memory (s : State) (p : MatrixCopy) :
    (neonInitialized s p).memory = s.memory := rfl

theorem neon_initialized_locals (s : State) (p : MatrixCopy) (h : Arguments s p) :
    NeonColumnLocals (neonInitialized s p) p p.cols := by
  constructor
  · constructor <;> simp [neonInitialized, neonResets, neonDimensions, update,
      h.height, h.inputStride, h.outputStride]
  · simp [neonInitialized, neonResets, neonDimensions, update, h.width]
  · simp [neonInitialized, update]
  · simp [neonInitialized, update]
  · simp [neonInitialized, update]
  · simp [neonInitialized, update]

end Salty.Kernels.X32Transpose
