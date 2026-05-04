import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-poisson-optimal-cauchy-rescaling-kl-constant`. -/
theorem paper_xi_poisson_optimal_cauchy_rescaling_kl_constant :
    (∀ α : ℝ, 1 / 16 ≤ (1 / 2) * (1 / 4 - α / 2 + α ^ 2 / 2)) ∧
      (∀ α : ℝ,
        (1 / 2) * (1 / 4 - α / 2 + α ^ 2 / 2) = 1 / 16 ↔ α = 1 / 2) := by
  constructor
  · intro α
    have hdiff :
        (1 / 2) * (1 / 4 - α / 2 + α ^ 2 / 2) - 1 / 16 =
          (2 * α - 1) ^ 2 / 16 := by
      ring
    have hs : 0 ≤ (2 * α - 1) ^ 2 := sq_nonneg (2 * α - 1)
    nlinarith
  · intro α
    constructor
    · intro hα
      have hdiff :
          (1 / 2) * (1 / 4 - α / 2 + α ^ 2 / 2) - 1 / 16 =
            (2 * α - 1) ^ 2 / 16 := by
        ring
      have hs : (2 * α - 1) ^ 2 = 0 := by
        nlinarith
      have hlin : 2 * α - 1 = 0 := sq_eq_zero_iff.mp hs
      nlinarith
    · intro hα
      rw [hα]
      norm_num

end Omega.Zeta
