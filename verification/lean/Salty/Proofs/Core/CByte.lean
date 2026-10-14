import Salty.Model.CByte
import Salty.Proofs.Core.Memory
import Salty.Proofs.Core.ByteISA
import Salty.Proofs.Core.QuantizedISA
import Salty.Proofs.Core.QuantizedLeakyISA
import Salty.Proofs.Core.QuantizedAddISA
import Salty.Proofs.Core.QuantizedUAddISA
import Salty.Proofs.Core.ReductionISA
import Salty.Proofs.Core.WideningISA

set_option maxHeartbeats 2000000

/-! A deliberately small, executable C/intrinsic model. This is not a C standard
semantics or a verified compiler frontend. The extractor's supported AST fragment
and intrinsic interface form a named, reviewable trusted bridge. Byte vectors
retain a lane-width tag so reinterpretation and little-endian lane stores are
explicit. Every byte access checks permissions. -/
namespace Salty.CByte

theorem Exec.deterministic {cfg : Config} {code : Stmt} {s a b : State}
    (ha : Exec cfg code s a) (hb : Exec cfg code s b) : a = b := by
  induction ha generalizing b with
  | skip => cases hb; rfl
  | assign h =>
    cases hb with
    | assign h' => rw [h] at h'; cases h'; rfl
  | effect he hm =>
    cases hb with
    | effect he' hm' => rw [he] at he'; cases he'; rw [hm] at hm'; cases hm'; rfl
  | seq _ _ ih1 ih2 =>
    cases hb with
    | seq h1 h2 => have eq := ih1 h1; subst eq; exact ih2 h2
  | yes he ht _ ih =>
    cases hb with
    | yes he' ht' h => rw [he] at he'; cases he'; exact ih h
    | no he' ht' _ => rw [he] at he'; cases he'; rw [ht] at ht'; contradiction
  | no he ht _ ih =>
    cases hb with
    | no he' ht' h => rw [he] at he'; cases he'; exact ih h
    | yes he' ht' _ => rw [he] at he'; cases he'; rw [ht] at ht'; contradiction
  | done he ht =>
    cases hb with
    | done => rfl
    | more he' ht' _ _ => rw [he] at he'; cases he'; rw [ht] at ht'; contradiction
  | more he ht _ _ ih1 ih2 =>
    cases hb with
    | done he' ht' => rw [he] at he'; cases he'; rw [ht] at ht'; contradiction
    | more he' ht' h1 h2 =>
      rw [he] at he'; cases he'
      have eq := ih1 h1
      subst eq
      exact ih2 h2

theorem run_sound {cfg : Config} {fuel : Nat} {code : Stmt} {s t : State}
    (h : run cfg fuel code s = some t) : Exec cfg code s t := by
  induction fuel generalizing code s t with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases code with
    | skip => simp only [run, Option.some.injEq] at h; subst t; exact .skip
    | assign name e =>
      simp only [run, Functor.map, Option.map_eq_some_iff] at h
      obtain ⟨v, he, rfl⟩ := h
      exact .assign he
    | effect op args =>
      simp only [run, bind, pure, Option.bind_eq_some_iff] at h
      obtain ⟨vs, he, m, hm, ht⟩ := h
      cases ht
      exact .effect he hm
    | seq a b =>
      simp only [run, bind, pure, Option.bind_eq_some_iff] at h
      obtain ⟨u, ha, hb⟩ := h
      exact .seq (ih ha) (ih hb)
    | branch e a b =>
      simp only [run, bind, pure, Option.bind_eq_some_iff] at h
      obtain ⟨v, he, test, ht, hrun⟩ := h
      cases test
      · exact .no he ht (ih hrun)
      · exact .yes he ht (ih hrun)
    | loop e body =>
      simp only [run, bind, pure, Option.bind_eq_some_iff] at h
      obtain ⟨v, he, test, ht, hrun⟩ := h
      cases test
      · cases hrun; exact .done he ht
      · simp only [Bool.true_eq, ↓reduceIte, bind, Option.bind_eq_some_iff] at hrun
        obtain ⟨u, hb, hl⟩ := hrun
        exact .more he ht (ih hb) (ih hl)

end Salty.CByte
