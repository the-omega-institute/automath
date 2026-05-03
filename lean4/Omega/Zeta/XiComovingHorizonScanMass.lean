import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

set_option linter.unusedVariables false

/-- Paper label: `cor:xi-comoving-horizon-scan-mass`. -/
theorem paper_xi_comoving_horizon_scan_mass {ι : Type*} [Fintype ι]
    (m δ γ : ι → ℝ) :
    (∑ j, 4 * Real.pi * m j * δ j / (1 + δ j)) =
      4 * Real.pi * ∑ j, m j * δ j / (1 + δ j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [mul_div_assoc, mul_div_assoc, mul_assoc]

end Omega.Zeta
