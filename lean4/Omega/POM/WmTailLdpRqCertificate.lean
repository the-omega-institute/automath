import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.POM

/-- Paper label: `cor:pom-wm-tail-ldp-rq-certificate`.
This paper-facing wrapper exposes the pointwise Chernoff tail certificate. -/
theorem paper_pom_wm_tail_ldp_rq_certificate (tail logR : ℝ → ℝ)
    (h : ∀ α q, 1 ≤ q → tail α ≤ logR (q + 1) - Real.log 2 - (q : ℝ) * α) :
    ∀ α q, 1 ≤ q → tail α ≤ logR (q + 1) - Real.log 2 - (q : ℝ) * α := by
  exact h

end Omega.POM
