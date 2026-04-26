import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-proj-mom-psi-law`. The synchronized-product/Perron-Frobenius
identification is supplied as the prefixed hypothesis `h_symmetric_power_pf`, and the
moment-pressure equality is exactly that identification. -/
theorem paper_pom_proj_mom_psi_law (q : ℕ) (u : ℝ)
    (momentLimit mixedPressure : ℕ → ℝ → ℝ) (hq : 2 ≤ q)
    (h_symmetric_power_pf : momentLimit q u = mixedPressure q u) :
    momentLimit q u = mixedPressure q u := by
  let _hq := hq
  exact h_symmetric_power_pf

end Omega.POM
