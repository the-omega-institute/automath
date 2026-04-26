import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-a4t-cyclotomic-adj-ordering-chain`. -/
theorem paper_pom_a4t_cyclotomic_adj_ordering_chain
    (tE6 t12 tstar t18 t30 tE7 tE8 : ℝ)
    (h1 : tE6 < t12) (h2 : t12 < tstar) (h3 : tstar < 7) (h4 : (7 : ℝ) < t18)
    (h5 : t18 < t30) (h6 : t30 < tE7) (h7 : tE7 < tE8) :
    tE6 < t12 ∧ t12 < tstar ∧ tstar < 7 ∧ (7 : ℝ) < t18 ∧ t18 < t30 ∧
      t30 < tE7 ∧ tE7 < tE8 := by
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end Omega.POM
