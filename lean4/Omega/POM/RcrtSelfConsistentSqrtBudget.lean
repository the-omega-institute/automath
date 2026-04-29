import Omega.POM.RcrtPressureReductionLaw

namespace Omega.POM

/-- Paper label: `cor:pom-rcrt-self-consistent-sqrt-budget`. -/
theorem paper_pom_rcrt_self_consistent_sqrt_budget
    (D : pom_rcrt_pressure_reduction_law_data) :
    D.baseMoment / (D.P : ℝ) ^ (D.q - 1) ≤ D.refinedMoment ∧
      D.refinedMoment ≤ D.baseMoment := by
  exact ⟨D.moment_lower, D.moment_upper⟩

end Omega.POM
