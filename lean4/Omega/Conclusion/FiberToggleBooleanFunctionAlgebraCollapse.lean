import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The Boolean cube of fiber-toggle states. -/
abbrev conclusion_fiber_toggle_boolean_function_algebra_collapse_cube (n : ℕ) :=
  Fin n → Bool

/-- The finite function algebra on the Boolean cube. -/
abbrev conclusion_fiber_toggle_boolean_function_algebra_collapse_algebra (n : ℕ) :=
  conclusion_fiber_toggle_boolean_function_algebra_collapse_cube n → ℚ

/-- The Boolean rank/classifying statistic: the cardinality of the `true` fiber. -/
def conclusion_fiber_toggle_boolean_function_algebra_collapse_rank {n : ℕ}
    (x : conclusion_fiber_toggle_boolean_function_algebra_collapse_cube n) : ℕ :=
  (Finset.univ.filter fun i => x i).card

/-- Evaluation idempotent at a Boolean-cube point. -/
def conclusion_fiber_toggle_boolean_function_algebra_collapse_evalIdempotent {n : ℕ}
    (x y : conclusion_fiber_toggle_boolean_function_algebra_collapse_cube n) : ℚ :=
  if y = x then 1 else 0

/-- Concrete finite Boolean function-algebra collapse statement. -/
def conclusion_fiber_toggle_boolean_function_algebra_collapse_statement : Prop :=
  (∀ n : ℕ,
      Fintype.card (conclusion_fiber_toggle_boolean_function_algebra_collapse_cube n) =
        2 ^ n) ∧
    (∀ n : ℕ,
      Nonempty
        (Module.Basis (conclusion_fiber_toggle_boolean_function_algebra_collapse_cube n) ℚ
          (conclusion_fiber_toggle_boolean_function_algebra_collapse_algebra n))) ∧
    (∀ n : ℕ,
      Module.finrank ℚ (conclusion_fiber_toggle_boolean_function_algebra_collapse_algebra n) =
        2 ^ n) ∧
    (∀ n : ℕ,
      Nonempty
        (conclusion_fiber_toggle_boolean_function_algebra_collapse_algebra n ≃ₐ[ℚ]
          (Fin (2 ^ n) → ℚ))) ∧
    (∀ (n : ℕ) (x : conclusion_fiber_toggle_boolean_function_algebra_collapse_cube n),
      (conclusion_fiber_toggle_boolean_function_algebra_collapse_evalIdempotent x *
          conclusion_fiber_toggle_boolean_function_algebra_collapse_evalIdempotent x) =
        conclusion_fiber_toggle_boolean_function_algebra_collapse_evalIdempotent x) ∧
    (∀ (n : ℕ) (x y : conclusion_fiber_toggle_boolean_function_algebra_collapse_cube n),
      conclusion_fiber_toggle_boolean_function_algebra_collapse_rank x =
          conclusion_fiber_toggle_boolean_function_algebra_collapse_rank y ↔
        (Finset.univ.filter fun i => x i).card = (Finset.univ.filter fun i => y i).card)

private lemma conclusion_fiber_toggle_boolean_function_algebra_collapse_cube_card (n : ℕ) :
    Fintype.card (conclusion_fiber_toggle_boolean_function_algebra_collapse_cube n) =
      2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

private lemma conclusion_fiber_toggle_boolean_function_algebra_collapse_idempotent
    (n : ℕ) (x : conclusion_fiber_toggle_boolean_function_algebra_collapse_cube n) :
    (conclusion_fiber_toggle_boolean_function_algebra_collapse_evalIdempotent x *
        conclusion_fiber_toggle_boolean_function_algebra_collapse_evalIdempotent x) =
      conclusion_fiber_toggle_boolean_function_algebra_collapse_evalIdempotent x := by
  funext y
  by_cases hy : y = x <;>
    simp [conclusion_fiber_toggle_boolean_function_algebra_collapse_evalIdempotent, hy]

/-- Paper label: `thm:conclusion-fiber-toggle-boolean-function-algebra-collapse`. -/
theorem paper_conclusion_fiber_toggle_boolean_function_algebra_collapse :
    conclusion_fiber_toggle_boolean_function_algebra_collapse_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact conclusion_fiber_toggle_boolean_function_algebra_collapse_cube_card
  · intro n
    exact ⟨Pi.basisFun ℚ (conclusion_fiber_toggle_boolean_function_algebra_collapse_cube n)⟩
  · intro n
    rw [Module.finrank_fintype_fun_eq_card,
      conclusion_fiber_toggle_boolean_function_algebra_collapse_cube_card]
  · intro n
    let e :
        conclusion_fiber_toggle_boolean_function_algebra_collapse_cube n ≃ Fin (2 ^ n) :=
      Fintype.equivOfCardEq
        (by
          simp [Fintype.card_fin,
            conclusion_fiber_toggle_boolean_function_algebra_collapse_cube_card n])
    exact ⟨AlgEquiv.piCongrLeft ℚ (fun _ : Fin (2 ^ n) => ℚ) e⟩
  · exact conclusion_fiber_toggle_boolean_function_algebra_collapse_idempotent
  · intro n x y
    rfl

end Omega.Conclusion
