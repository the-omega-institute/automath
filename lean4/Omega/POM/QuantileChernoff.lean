import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-quantile-chernoff`.
Rearranging the exponential-moment bound by the positive factor
`exp (((q - 1) * m * gamma))` yields the stated Chernoff tail estimate. -/
theorem paper_pom_quantile_chernoff (m q : ℕ) (Sq gamma tailProb : ℝ)
    (hMoment :
      tailProb * Real.exp ((((q - 1 : ℕ) : ℝ) * (m : ℝ) * gamma)) ≤ Sq / (2 : ℝ) ^ m) :
    tailProb ≤ Real.exp (-(((q - 1 : ℕ) : ℝ) * (m : ℝ) * gamma)) * (Sq / (2 : ℝ) ^ m) := by
  let t : ℝ := (((q - 1 : ℕ) : ℝ) * (m : ℝ) * gamma)
  have hexp_pos : 0 < Real.exp t := Real.exp_pos t
  have hdiv : tailProb ≤ (Sq / (2 : ℝ) ^ m) / Real.exp t := by
    exact (le_div_iff₀ hexp_pos).2 <| by simpa [t, mul_comm, mul_left_comm, mul_assoc] using hMoment
  simpa [div_eq_mul_inv, t, Real.exp_neg, mul_comm, mul_left_comm, mul_assoc] using hdiv

end Omega.POM
