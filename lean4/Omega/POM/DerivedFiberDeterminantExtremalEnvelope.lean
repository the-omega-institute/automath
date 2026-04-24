import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Sqrt
import Omega.POM.DerivedFiberSingleStieltjesHistogramRecovery
import Omega.POM.FiberSpectrumStieltjesRigidityDeterminantSchatten
import Omega.POM.ShannonEntropySqueeze

namespace Omega.POM

open Polynomial

/-- Paper label: `thm:derived-fiber-determinant-extremal-envelope`. -/
def derived_fiber_determinant_extremal_envelope_statement : Prop :=
  (∀ d₁ d₂ d₃ : ℕ, 0 < d₁ → 0 < d₂ → 0 < d₃ →
    fiberSpectrumDeterminantPotential d₁ d₂ d₃ =
      (1 + C (d₁ : ℚ) * X) * (1 + C (d₂ : ℚ) * X) * (1 + C (d₃ : ℚ) * X) ∧
    (∀ t : ℚ, fiberSpectrumStieltjes d₁ d₂ d₃ t =
      (d₁ : ℚ) / (1 + t * d₁) + (d₂ : ℚ) / (1 + t * d₂) + (d₃ : ℚ) / (1 + t * d₃)) ∧
    (∀ d : ℕ, fiberSpectrumResidueMultiplicity d₁ d₂ d₃ d = [d₁, d₂, d₃].count d) ∧
    (∀ k : ℕ, fiberSpectrumSchattenEvenData d₁ d₂ d₃ k = fiberSpectrumNegativePowerSum d₁ d₂ d₃ k) ∧
    cubicFromPowerSums
      (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 1)
      (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 2)
      (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 3) =
        reciprocalSpectrumPolynomial d₁ d₂ d₃) ∧
  pomRenyiTwoRate ≤ pomShannonRateLower ∧
  pomShannonRateLower ≤ pomShannonRateUpper ∧
  pomShannonRateUpper ≤ Real.log ((1 + Real.sqrt 5) / 2) ∧
  pomShannonRateLower = pomRenyiTwoRate ∧
  pomShannonRateUpper = Real.log ((1 + Real.sqrt 5) / 2)

theorem paper_derived_fiber_determinant_extremal_envelope :
    derived_fiber_determinant_extremal_envelope_statement := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro d₁ d₂ d₃ h₁ h₂ h₃
    have h :=
      paper_pom_fiber_spectrum_stieltjes_rigidity_determinant_schatten d₁ d₂ d₃ h₁ h₂ h₃
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  · exact paper_pom_shannon_entropy_squeeze.1
  · exact paper_pom_shannon_entropy_squeeze.2.1
  · exact paper_pom_shannon_entropy_squeeze.2.2

end Omega.POM
