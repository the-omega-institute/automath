import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-poisson-cauchy-l2-optimal-scale-halving`.
The strictly convex quadratic `A - 2 a B + C a^2` has the unique minimizer
characterized by the normal equation `C * a = B`. -/
theorem paper_xi_poisson_cauchy_l2_optimal_scale_halving (A B C : ℝ) (hC : 0 < C) :
    ∃! a : ℝ,
      (∀ b : ℝ, A - 2 * a * B + C * a ^ 2 ≤ A - 2 * b * B + C * b ^ 2) ∧
        C * a = B := by
  refine ⟨B / C, ?_, ?_⟩
  · constructor
    · intro b
      have hsq : 0 ≤ C * (b - B / C) ^ 2 :=
        mul_nonneg (le_of_lt hC) (sq_nonneg _)
      have hdiff :
          A - 2 * b * B + C * b ^ 2 -
              (A - 2 * (B / C) * B + C * (B / C) ^ 2) =
            C * (b - B / C) ^ 2 := by
        field_simp [hC.ne']
        ring
      nlinarith
    · field_simp [hC.ne']
  · intro y hy
    have hyC : C * y = B := hy.2
    have ha : C * (B / C) = B := by
      field_simp [hC.ne']
    nlinarith

end Omega.Zeta
