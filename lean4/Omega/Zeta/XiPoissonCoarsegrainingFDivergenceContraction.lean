import Mathlib.Tactic

namespace Omega.Zeta

noncomputable def xi_poisson_coarsegraining_f_divergence_contraction_poisson_kernel
    (_ : Fin 2) : ℝ :=
  1 / 2

noncomputable def xi_poisson_coarsegraining_f_divergence_contraction_conditional_expectation
    (u : Fin 2 → ℝ) : ℝ :=
  (u 0 + u 1) / 2

noncomputable def xi_poisson_coarsegraining_f_divergence_contraction_f_divergence
    (u : Fin 2 → ℝ) : ℝ :=
  ((u 0) ^ 2 + (u 1) ^ 2) / 2

def xi_poisson_coarsegraining_f_divergence_contraction_statement : Prop :=
  (∀ i : Fin 2, 0 < xi_poisson_coarsegraining_f_divergence_contraction_poisson_kernel i) ∧
    (∀ u : Fin 2 → ℝ,
      (xi_poisson_coarsegraining_f_divergence_contraction_conditional_expectation u) ^ 2 ≤
        xi_poisson_coarsegraining_f_divergence_contraction_f_divergence u) ∧
    (∀ u : Fin 2 → ℝ, u 0 ≠ u 1 →
      (xi_poisson_coarsegraining_f_divergence_contraction_conditional_expectation u) ^ 2 <
        xi_poisson_coarsegraining_f_divergence_contraction_f_divergence u)

/-- Paper label: `prop:xi-poisson-coarsegraining-f-divergence-contraction`.
The two-point coarse-graining kernel is positive, the coarse-grained likelihood ratio is the
conditional expectation `(u₀ + u₁)/2`, and Jensen for the strictly convex function `x ↦ x²`
gives contraction, with strictness unless the two likelihood ratios already agree. -/
theorem paper_xi_poisson_coarsegraining_f_divergence_contraction :
    xi_poisson_coarsegraining_f_divergence_contraction_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    norm_num [xi_poisson_coarsegraining_f_divergence_contraction_poisson_kernel]
  · intro u
    dsimp [xi_poisson_coarsegraining_f_divergence_contraction_conditional_expectation,
      xi_poisson_coarsegraining_f_divergence_contraction_f_divergence]
    have hsq : 0 ≤ (u 0 - u 1) ^ 2 := sq_nonneg (u 0 - u 1)
    nlinarith
  · intro u hne
    dsimp [xi_poisson_coarsegraining_f_divergence_contraction_conditional_expectation,
      xi_poisson_coarsegraining_f_divergence_contraction_f_divergence]
    have hsq : 0 < (u 0 - u 1) ^ 2 := by
      apply sq_pos_of_ne_zero
      exact sub_ne_zero.mpr hne
    nlinarith

end Omega.Zeta
