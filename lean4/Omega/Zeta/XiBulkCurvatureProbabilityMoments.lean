import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Equal-weight average of the translated logistic centers. -/
noncomputable def xi_bulk_curvature_probability_moments_centerAverage {κ : ℕ}
    (σ : Fin κ → ℝ) : ℝ :=
  (κ : ℝ)⁻¹ * ∑ j : Fin κ, σ j

/-- Discrete variance of the translated logistic centers. -/
noncomputable def xi_bulk_curvature_probability_moments_discreteVariance {κ : ℕ}
    (σ : Fin κ → ℝ) : ℝ :=
  (κ : ℝ)⁻¹ *
    ∑ j : Fin κ, (σ j - xi_bulk_curvature_probability_moments_centerAverage σ) ^ 2

/-- Paper label: `cor:xi-bulk-curvature-probability-moments`.
The normalized bulk-curvature density is represented by an equal-weight finite mixture of
translated centered logistic kernels. Once the centered logistic kernel has first moment `0` and
second centered moment `π^2 / 3`, the mixture mean is the average translated center and the
mixture variance is the universal logistic variance plus the discrete variance of the centers. -/
theorem paper_xi_bulk_curvature_probability_moments (κ : ℕ) (hκ : 0 < κ)
    (σ : Fin κ → ℝ) :
    (κ : ℝ)⁻¹ * ∑ j : Fin κ, σ j =
        xi_bulk_curvature_probability_moments_centerAverage σ ∧
      (κ : ℝ)⁻¹ *
          ∑ j : Fin κ,
            ((Real.pi ^ 2 / 3) +
              (σ j - xi_bulk_curvature_probability_moments_centerAverage σ) ^ 2) =
        Real.pi ^ 2 / 3 + xi_bulk_curvature_probability_moments_discreteVariance σ := by
  have hκ_ne : (κ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hκ)
  refine ⟨rfl, ?_⟩
  simp only [xi_bulk_curvature_probability_moments_discreteVariance, Finset.sum_add_distrib,
    mul_add]
  have hcard : (∑ _j : Fin κ, (Real.pi ^ 2 / 3 : ℝ)) = (κ : ℝ) * (Real.pi ^ 2 / 3) := by
    simp
  rw [hcard]
  field_simp [hκ_ne]

end Omega.Zeta
