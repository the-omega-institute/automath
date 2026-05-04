import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-cauchy-poisson-chi2-hellinger-sixth-order`. -/
theorem paper_xi_cauchy_poisson_chi2_hellinger_sixth_order (σ μ3 μ4 : ℝ) :
    (let leading := fun f2 : ℝ => f2 * σ ^ 4 / 8
     let sixth := fun f2 f3 : ℝ =>
       f2 * (3 * μ3 ^ 2 / 32 - σ ^ 2 * μ4 / 8) - f3 * σ ^ 6 / 64
     leading 2 = σ ^ 4 / 4 ∧
       sixth 2 0 = 3 * μ3 ^ 2 / 16 - σ ^ 2 * μ4 / 4 ∧
       leading (1 / 2) = σ ^ 4 / 16 ∧
       sixth (1 / 2) (-(3 / 4)) =
         3 * μ3 ^ 2 / 64 - σ ^ 2 * μ4 / 16 + 3 * σ ^ 6 / 256) := by
  norm_num
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring

end Omega.Zeta
