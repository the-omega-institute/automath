import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-oracle-critical-budget-zeckendorf-plus-gap`.
The Zeckendorf baseline and entropy-gap decomposition follow by substituting the
KL entropy-rate identity into the critical-budget identities. -/
theorem paper_pom_oracle_critical_budget_zeckendorf_plus_gap
    (a1 betaCrit gamma logPhi logTwo : ℝ)
    (hgamma : gamma = logPhi - (logTwo - a1))
    (hbeta : betaCrit = a1 / logTwo) (hlogTwo : logTwo ≠ 0) :
    a1 = (logTwo - logPhi) + gamma ∧
      betaCrit = 1 - logPhi / logTwo + gamma / logTwo := by
  constructor
  · linarith
  · have ha1 : a1 = logTwo - logPhi + gamma := by
      linarith
    rw [hbeta, ha1]
    field_simp [hlogTwo]

end Omega.POM
