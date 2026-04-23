import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.POM

/-- Paper label: `cor:pom-mu-secant-audit`. The secant-slope bounds at `q = 1`, together with the
endpoint identities `τ(0) = log r₀`, `τ(1) = log 2`, and `τ(2) = log r₂`, rewrite directly into
the logarithmic audit interval for `μ`. -/
theorem paper_pom_mu_secant_audit (tau : ℕ → ℝ) (μ r0 r2 : ℝ) (hr0 : 0 < r0) (hr2 : 0 < r2)
    (hsecant : tau 1 - tau 0 ≤ μ ∧ μ ≤ tau 2 - tau 1) (htau0 : tau 0 = Real.log r0)
    (htau1 : tau 1 = Real.log 2) (htau2 : tau 2 = Real.log r2) :
    Real.log (2 / r0) ≤ μ ∧ μ ≤ Real.log (r2 / 2) := by
  rcases hsecant with ⟨hleft, hright⟩
  have hr0ne : r0 ≠ 0 := ne_of_gt hr0
  have hr2ne : r2 ≠ 0 := ne_of_gt hr2
  refine ⟨?_, ?_⟩
  · calc
      Real.log (2 / r0) = Real.log 2 - Real.log r0 := by
        rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hr0ne]
      _ = tau 1 - tau 0 := by rw [htau1, htau0]
      _ ≤ μ := hleft
  · calc
      μ ≤ tau 2 - tau 1 := hright
      _ = Real.log r2 - Real.log 2 := by rw [htau2, htau1]
      _ = Real.log (r2 / 2) := by
        rw [← Real.log_div hr2ne (by norm_num : (2 : ℝ) ≠ 0)]

end Omega.POM
