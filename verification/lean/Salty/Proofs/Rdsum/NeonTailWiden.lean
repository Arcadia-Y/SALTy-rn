import Salty.Proofs.Rdsum.NeonTailInner

namespace Salty.Kernels.Rdsum
open CByte ReductionISA
set_option maxHeartbeats 1000000

def neonTailWiden (kind : Interpretation) : Stmt := takeStatements 2 (dropStatements 2 (neonBatch kind false))

theorem neon_tail_widen_shape (kind : Interpretation) : neonTailWiden kind =
    .seq (.assign "vacc0_2" (.call (rowHalfPrim kind)
      [.var "vacc0_2", .call .lowI16x4 [.var (neonHalfName kind false 0)]]))
    (.seq (.assign "vacc1" (.call (rowHalfPrim kind)
      [.var "vacc1", .call .highI16x4 [.var (neonHalfName kind false 0)]])) .skip) := by
  cases kind <;> rfl

def neonTailWidened (s : State) (values : List (BitVec 32)) : State :=
  update (update s "vacc0_2" (.words32 (values.take 4))) "vacc1" (.words32 (values.drop 4))

theorem neon_tail_widen_exec (kind : Interpretation) (cfg : Config) (s : State)
    (acc : List (BitVec 32)) (half : List (BitVec 16)) (ha : acc.length = 8) (hh : half.length = 8)
    (low : s.locals "vacc0_2" = some (.words32 (acc.take 4)))
    (high : s.locals "vacc1" = some (.words32 (acc.drop 4)))
    (halfLoc : s.locals (neonHalfName kind false 0) = some (.halfwords half)) :
    Exec cfg (neonTailWiden kind) s (neonTailWidened s (WideningISA.widenAdd32 kind acc half)) := by
  rw [neon_tail_widen_shape]
  cases kind <;> simp only [neonHalfName, Bool.false_eq_true, ↓reduceIte] at halfLoc
  all_goals
    apply run_sound (fuel := 5)
    simp [run, eval, intrinsic, saturatingIntrinsic, selectionIntrinsic, integerArithmeticIntrinsic, rowHalfPrim, neonHalfName,
      low, high, halfLoc, ha, hh, update, neonTailWidened, WideningISA.widenAdd32,
      List.take_zipWith, List.drop_zipWith]

/-- NEON's two four-word widening adds implement the same exact eight-column
batch sum as the scalable widening instruction. -/
theorem neon_tail_inner_widen_correct (kind : Interpretation) (cfg : Config) (s : State)
    (input zero : Address) (stride first rows : Nat) (pointers : Nat → Address)
    (initial : Nat → BitVec 32) (positive : 0 < rows) (bounded : rows ≤ 252)
    (loc : NeonTailLocals kind s pointers zero rows (7*stride) ((List.range 8).map (fun _ => 0)))
    (low : s.locals "vacc0_2" = some (.words32 (((List.range 8).map initial).take 4)))
    (high : s.locals "vacc1" = some (.words32 (((List.range 8).map initial).drop 4)))
    (safe : GroupsSafe s.memory zero 8 (7*stride) ((rows+6)/7) pointers rows)
    (zeros : ∀ column, column < 8 → s.memory.data (zero+BitVec.ofNat 64 column) = 0)
    (ptrs : ∀ (i : Nat), i < 7 → i < rows → pointers i = input+BitVec.ofNat 64 ((first+i)*stride)) :
    ∃ t, Exec cfg (.seq (neonInnerLoop kind false) (neonTailWiden kind)) s t ∧ t.memory = s.memory ∧
      let values := (List.range 8).map (fun column => initial column+intervalSum kind s.memory input stride first rows column);
      t.locals "vacc0_2" = some (.words32 (values.take 4)) ∧
      t.locals "vacc1" = some (.words32 (values.drop 4)) ∧
      (∀ i, i < 7 → t.locals (neonRowName false i) = some (.pointer
        ((groupFold kind s.memory zero 8 (7*stride) ((rows+6)/7) pointers rows
          ((List.range 8).map (fun _ => 0))).pointers i))) := by
  let result := groupFold kind s.memory zero 8 (7*stride) ((rows+6)/7) pointers rows
    ((List.range 8).map (fun _ => 0))
  obtain ⟨u,loop,mem,uloc⟩ := neon_tail_inner_total kind cfg s ((rows+6)/7) pointers zero rows (7*stride)
    ((List.range 8).map (fun _ => 0)) (by simp) (group_count_ceiling rows) (by omega) loc safe
  have lo : u.locals "vacc0_2" = some (.words32 (((List.range 8).map initial).take 4)) :=
    (loop.locals_frame _ (by cases kind <;> rfl)).trans low
  have hi : u.locals "vacc1" = some (.words32 (((List.range 8).map initial).drop 4)) :=
    (loop.locals_frame _ (by cases kind <;> rfl)).trans high
  have halfLen : result.acc.length = 8 := groupFold_length kind s.memory zero 8 (7*stride)
    ((rows+6)/7) pointers rows _ (by simp)
  let wideValues := WideningISA.widenAdd32 kind ((List.range 8).map initial) result.acc
  let t := neonTailWidened u wideValues
  have wide : Exec cfg (neonTailWiden kind) u t := neon_tail_widen_exec kind cfg u _ result.acc
    (by simp) halfLen lo hi uloc.acc
  have exactSum : wideValues = (List.range 8).map
      (fun column => initial column+intervalSum kind s.memory input stride first rows column) :=
    widen_groupFold_original kind s.memory input zero 8 stride ((rows+6)/7) first rows pointers initial
      (group_count_ceiling rows) (by have := group_count_small rows bounded; omega) zeros ptrs
  refine ⟨t,.seq loop wide,mem,?_,?_,?_⟩
  · simp [t, neonTailWidened, update, exactSum]
  · simp [t, neonTailWidened, update, exactSum]
  · intro i hi
    exact (wide.locals_frame _ (by
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases kind <;> rfl)).trans (uloc.rows i hi)

end Salty.Kernels.Rdsum
