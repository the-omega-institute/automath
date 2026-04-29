import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-error-exponent-triple-identity`. -/
theorem paper_pom_error_exponent_triple_identity (Cphi I0 Dhalf log2Phi : ℝ)
    (hC : Cphi = (3 / 2) * log2Phi - 1) (hI : I0 = (3 / 2) * log2Phi - 1)
    (hD : Dhalf = 3 * log2Phi - 2) :
    Cphi = I0 ∧ I0 = (1 / 2) * Dhalf ∧ Cphi = (3 / 2) * log2Phi - 1 := by
  refine ⟨?_, ?_, hC⟩
  · rw [hC, hI]
  · rw [hI, hD]
    ring

end Omega.POM
