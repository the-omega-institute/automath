import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-a2-strict-rh-certificate`. The interval certificate
`r₂ > 9/4` gives `sqrt r₂ > 3/2`, so the sub-spectral bound `Lambda₂ ≤ 5/4`
lies strictly below the square-root threshold. -/
theorem paper_pom_a2_strict_rh_certificate (r2 Lambda2 : ℝ) (hr2 : (9 : ℝ) / 4 < r2)
    (hLambda : Lambda2 ≤ (5 : ℝ) / 4) : Lambda2 < Real.sqrt r2 := by
  have hsquare : ((3 : ℝ) / 2) ^ (2 : ℕ) < r2 := by
    norm_num at hr2 ⊢
    exact hr2
  have hsqrt : (3 : ℝ) / 2 < Real.sqrt r2 := by
    have hmono :
        Real.sqrt (((3 : ℝ) / 2) ^ (2 : ℕ)) < Real.sqrt r2 :=
      Real.sqrt_lt_sqrt (sq_nonneg ((3 : ℝ) / 2)) hsquare
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)] using
      hmono
  nlinarith

end Omega.POM
