import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- At `p = 5`, the first-order gap law can be inverted for the effective defect parameter because
`1 - cos (2π / 5)` is nonzero. The proof specializes the denominator using the exact value of
`cos (π / 5)` and then clears denominators algebraically.
    cor:arity-335-eps-eff-inversion -/
theorem paper_arity_335_eps_eff_inversion
    (rho lambda : ℝ) (hlambda : lambda ≠ 0) :
    let epsEff := (1 - rho / lambda) / (1 - Real.cos (2 * Real.pi / 5))
    1 - rho / lambda = epsEff * (1 - Real.cos (2 * Real.pi / 5)) := by
  dsimp
  have hden : 1 - Real.cos (2 * Real.pi / 5) ≠ 0 := by
    have hrewrite : 2 * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
    rw [hrewrite, Real.cos_two_mul, Real.cos_pi_div_five]
    have hfive_nonneg : (0 : ℝ) ≤ 5 := by norm_num
    have hsq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt hfive_nonneg
    have hclosed :
        1 - (2 * ((1 + Real.sqrt 5) / 4) ^ 2 - 1) = (5 - Real.sqrt 5) / 4 := by
      nlinarith
    have hsqrt : Real.sqrt 5 < 5 := by
      nlinarith [Real.sq_sqrt hfive_nonneg]
    have hpos : 0 < (5 - Real.sqrt 5) / 4 := by
      nlinarith
    rw [hclosed]
    exact ne_of_gt hpos
  field_simp [hlambda, hden]

end Omega.Zeta
