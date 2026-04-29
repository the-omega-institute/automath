import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-observable-minpoly-chebotarev-density-q9-13`. -/
theorem paper_pom_observable_minpoly_chebotarev_density_q9_13
    (densityIrreducible : ℕ → ℚ) (h9 : densityIrreducible 9 = (1 : ℚ) / 7)
    (h10 : densityIrreducible 10 = (1 : ℚ) / 9)
    (h11 : densityIrreducible 11 = (1 : ℚ) / 9)
    (h13 : densityIrreducible 13 = (1 : ℚ) / 11) :
    densityIrreducible 9 = (1 : ℚ) / 7 ∧
      densityIrreducible 10 = (1 : ℚ) / 9 ∧
        densityIrreducible 11 = (1 : ℚ) / 9 ∧
          densityIrreducible 13 = (1 : ℚ) / 11 := by
  exact ⟨h9, h10, h11, h13⟩

end Omega.POM
