import Mathlib.Tactic
import Omega.CircleDimension.LeyangOrthogonalDualImaginaryProjection

namespace Omega.UnitCirclePhaseArithmetic

open Omega.CircleDimension

noncomputable section

/-- The orthogonal Lee--Yang dual gate on the halved angular variable. -/
noncomputable def leyang_orthogonal_dual_pushforward_density_formula_lambda (θ : ℝ) : ℝ :=
  1 / (4 * Real.sin (θ / 2) ^ 2)

/-- The explicit Haar-pushforward density on `[1/4, ∞)` coming from the orthogonal dual gate. -/
noncomputable def leyang_orthogonal_dual_pushforward_density_formula_density (lam : ℝ) : ℝ :=
  if (1 / 4 : ℝ) ≤ lam then 1 / (Real.pi * lam * Real.sqrt (4 * lam - 1)) else 0

/-- Paper label: `thm:leyang-orthogonal-dual-pushforward-density-formula`.
Halving the angular variable identifies the orthogonal dual gate with the chapter-local inverse
square channel, so the pushforward density is the explicit `1 / (π λ √(4 λ - 1))` law on
`[1/4, ∞)`. -/
theorem paper_leyang_orthogonal_dual_pushforward_density_formula :
    (∀ θ : ℝ,
      leyang_orthogonal_dual_pushforward_density_formula_lambda θ =
        1 / (4 * Real.sin (θ / 2) ^ 2)) ∧
      (∀ θ : ℝ,
        leyang_orthogonal_dual_pushforward_density_formula_lambda (2 * θ) =
          leyangDualInverseSquareGate θ) ∧
      (∀ θ : ℝ, Real.sin θ ≠ 0 →
        (1 : ℝ) / 4 ≤ leyang_orthogonal_dual_pushforward_density_formula_lambda (2 * θ)) ∧
      (∀ lam : ℝ,
        leyang_orthogonal_dual_pushforward_density_formula_density lam =
          if (1 / 4 : ℝ) ≤ lam then 1 / (Real.pi * lam * Real.sqrt (4 * lam - 1)) else 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ
    rfl
  · intro θ
    simp [leyang_orthogonal_dual_pushforward_density_formula_lambda, leyangDualInverseSquareGate]
  · intro θ hsin
    simpa [leyang_orthogonal_dual_pushforward_density_formula_lambda, leyangDualInverseSquareGate]
      using one_quarter_le_leyangDualInverseSquareGate θ hsin
  · intro lam
    rfl

end

end Omega.UnitCirclePhaseArithmetic
