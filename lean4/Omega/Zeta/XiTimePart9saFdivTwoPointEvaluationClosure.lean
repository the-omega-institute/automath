import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

open scoped goldenRatio

/-- High likelihood-ratio atom in the golden two-point collapse. -/
noncomputable def xi_time_part9sa_fdiv_two_point_evaluation_closure_a : ℝ :=
  Real.goldenRatio ^ 2 / Real.sqrt 5

/-- Low likelihood-ratio atom in the golden two-point collapse. -/
noncomputable def xi_time_part9sa_fdiv_two_point_evaluation_closure_b : ℝ :=
  Real.goldenRatio / Real.sqrt 5

/-- The limiting two-point `f`-divergence evaluation functional. -/
noncomputable def xi_time_part9sa_fdiv_two_point_evaluation_closure_eval
    (f : ℝ → ℝ) : ℝ :=
  Real.goldenRatio⁻¹ * f xi_time_part9sa_fdiv_two_point_evaluation_closure_a +
    (Real.goldenRatio⁻¹) ^ 2 * f xi_time_part9sa_fdiv_two_point_evaluation_closure_b

/-- Paper label: `cor:xi-time-part9sa-fdiv-two-point-evaluation-closure`.
The two-atom limit is a linear evaluation functional, so agreement of two generators at the two
likelihood-ratio atoms forces equality of their limiting divergences. -/
theorem paper_xi_time_part9sa_fdiv_two_point_evaluation_closure :
    (∀ f : ℝ → ℝ,
      xi_time_part9sa_fdiv_two_point_evaluation_closure_eval f =
        Real.goldenRatio⁻¹ * f xi_time_part9sa_fdiv_two_point_evaluation_closure_a +
          (Real.goldenRatio⁻¹) ^ 2 *
            f xi_time_part9sa_fdiv_two_point_evaluation_closure_b) ∧
      (∀ f g : ℝ → ℝ,
        f xi_time_part9sa_fdiv_two_point_evaluation_closure_a =
            g xi_time_part9sa_fdiv_two_point_evaluation_closure_a →
          f xi_time_part9sa_fdiv_two_point_evaluation_closure_b =
            g xi_time_part9sa_fdiv_two_point_evaluation_closure_b →
            xi_time_part9sa_fdiv_two_point_evaluation_closure_eval f =
              xi_time_part9sa_fdiv_two_point_evaluation_closure_eval g) ∧
      (∀ (c d : ℝ) (f g : ℝ → ℝ),
        xi_time_part9sa_fdiv_two_point_evaluation_closure_eval
            (fun x => c * f x + d * g x) =
          c * xi_time_part9sa_fdiv_two_point_evaluation_closure_eval f +
            d * xi_time_part9sa_fdiv_two_point_evaluation_closure_eval g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    rfl
  · intro f g ha hb
    unfold xi_time_part9sa_fdiv_two_point_evaluation_closure_eval
    rw [ha, hb]
  · intro c d f g
    unfold xi_time_part9sa_fdiv_two_point_evaluation_closure_eval
    ring

end Omega.Zeta
