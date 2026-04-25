import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-critical-spectrum-gap-bounds`. -/
theorem paper_pom_diagonal_rate_critical_spectrum_gap_bounds
    (A C wMax wSecond mu2 : ℝ) (hC : 0 < C)
    (hlo : A / Real.sqrt wMax ≤ C * mu2)
    (hhi : C * mu2 ≤ A / Real.sqrt wSecond) :
    A / (C * Real.sqrt wMax) ≤ mu2 ∧
      mu2 ≤ A / (C * Real.sqrt wSecond) := by
  constructor
  · have hdiv :
        (A / Real.sqrt wMax) / C ≤ (C * mu2) / C :=
      div_le_div_of_nonneg_right hlo hC.le
    calc
      A / (C * Real.sqrt wMax) = (A / Real.sqrt wMax) / C := by
        field_simp [hC.ne']
      _ ≤ (C * mu2) / C := hdiv
      _ = mu2 := by
        field_simp [hC.ne']
  · have hdiv :
        (C * mu2) / C ≤ (A / Real.sqrt wSecond) / C :=
      div_le_div_of_nonneg_right hhi hC.le
    calc
      mu2 = (C * mu2) / C := by
        field_simp [hC.ne']
      _ ≤ (A / Real.sqrt wSecond) / C := hdiv
      _ = A / (C * Real.sqrt wSecond) := by
        field_simp [hC.ne']

end Omega.POM
