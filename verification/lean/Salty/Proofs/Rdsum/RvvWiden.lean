import Salty.Proofs.Rdsum.BatchArithmetic

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def accumulatorName : Interpretation → String
  | .signed => "vacc"
  | .unsigned => "vacc32"

def rvvWiden (kind : Interpretation) : Stmt :=
  firstStatement (dropStatements (match kind with | .signed => 2 | .unsigned => 4) (rvvBatches kind))

theorem rvv_widen_shape (kind : Interpretation) : rvvWiden kind =
    .assign (accumulatorName kind) (.call (rowHalfRVVPrim kind)
      [.var (accumulatorName kind), .var "vacc16", .var "vl"]) := by
  cases kind <;> rfl

theorem rvv_widen_exec (kind : Interpretation) (cfg : Config) (s : State)
    (width : Nat) (acc : List (BitVec 32)) (half : List (BitVec 16))
    (ha : acc.length = width) (hh : half.length = width) (cap : width ≤ cfg.capacity)
    (aloc : s.locals (accumulatorName kind) = some (.words32 acc))
    (hloc : s.locals "vacc16" = some (.halfwords half))
    (vl : s.locals "vl" = some (.integer width)) :
    Exec cfg (rvvWiden kind) s (update s (accumulatorName kind) (.words32 (WideningISA.widenAdd32 kind acc half))) := by
  rw [rvv_widen_shape]
  apply Exec.assign
  simp only [eval, aloc, hloc, vl, List.mapM_cons, List.mapM_nil, Option.bind_some, pure, bind]
  exact row_half_rvv_intrinsic kind cfg s.memory width acc half ha hh cap

/-- The extracted seven-row loop followed by its actual widening instruction
adds exactly the original row interval to each word accumulator. Preconditions
are memory geometry, zero-buffer contents and concrete local values, not an
assumed equivalence or an assumed arithmetic result. -/
theorem rvv_inner_widen_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero : Address) (width stride first rows : Nat) (pointers : Nat → Address)
    (initial : Nat → BitVec 32) (positive : 0 < rows) (bounded : rows ≤ 252) (cap : width ≤ cfg.capacity)
    (loc : GroupLocals s pointers zero rows width (7*stride) ((List.range width).map (fun _ => 0)))
    (aloc : s.locals (accumulatorName kind) = some (.words32 ((List.range width).map initial)))
    (safe : GroupsSafe s.memory zero width (7*stride) ((rows+6)/7) pointers rows)
    (zeros : ∀ column, column < width → s.memory.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < rows → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∃ t, Exec cfg (.seq (rvvInnerLoop kind) (rvvWiden kind)) s t ∧ t.memory = s.memory ∧
      t.locals (accumulatorName kind) = some (.words32 ((List.range width).map
        (fun column => initial column+intervalSum kind s.memory input stride first rows column))) ∧
      (∀ i, i < 7 → t.locals (rowName i) = some (.pointer
        ((groupFold kind s.memory zero width (7*stride) ((rows+6)/7) pointers rows
          ((List.range width).map (fun _ => 0))).pointers i))) := by
  let result := groupFold kind s.memory zero width (7*stride) ((rows+6)/7) pointers rows
    ((List.range width).map (fun _ => 0))
  obtain ⟨u,loop,mem,uloc⟩ := rvv_inner_total kind cfg s ((rows+6)/7) pointers zero rows width (7*stride)
    ((List.range width).map (fun _ => 0)) cap (by simp) (group_count_ceiling rows) (by omega) loc safe
  have acc : u.locals (accumulatorName kind) = some (.words32 ((List.range width).map initial)) :=
    (loop.locals_frame (accumulatorName kind) (by cases kind <;> rfl)).trans aloc
  have halfLen : result.acc.length = width := groupFold_length kind s.memory zero width (7*stride)
    ((rows+6)/7) pointers rows _ (by simp)
  let t := update u (accumulatorName kind) (.words32 (WideningISA.widenAdd32 kind
    ((List.range width).map initial) result.acc))
  have wide : Exec cfg (rvvWiden kind) u t := rvv_widen_exec kind cfg u width _ result.acc
    (by simp) halfLen cap acc uloc.acc uloc.vl
  refine ⟨t,.seq loop wide,mem,?_,?_⟩
  · simp only [t, update, ↓reduceIte]
    change some (Value.words32 (WideningISA.widenAdd32 kind ((List.range width).map initial) result.acc)) = _
    rw [widen_groupFold_original kind s.memory input zero width stride ((rows+6)/7) first rows pointers initial
      (group_count_ceiling rows) (by have := group_count_small rows bounded; omega) zeros ptrs]
  · intro i hi
    exact (wide.locals_frame (rowName i) (by
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases kind <;> rfl)).trans (uloc.rows i hi)

end Salty.Kernels.Rdsum
