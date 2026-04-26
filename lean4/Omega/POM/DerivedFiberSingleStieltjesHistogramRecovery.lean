import Omega.POM.FiberSpectrumStieltjesRigidityDeterminantSchatten

namespace Omega.POM

/-- A single Stieltjes potential recovers the three-point fiber histogram: its partial fractions are
the displayed Stieltjes expansion, residues recover multiplicities, and the even Schatten data are
the negative power sums of the reciprocal spectrum. -/
def derivedFiberSingleStieltjesHistogramRecoveryStatement : Prop :=
  ∀ d₁ d₂ d₃ : ℕ, 0 < d₁ → 0 < d₂ → 0 < d₃ →
    (∀ t : ℚ, fiberSpectrumStieltjes d₁ d₂ d₃ t =
      (d₁ : ℚ) / (1 + t * d₁) + (d₂ : ℚ) / (1 + t * d₂) + (d₃ : ℚ) / (1 + t * d₃)) ∧
    (∀ d : ℕ, fiberSpectrumResidueMultiplicity d₁ d₂ d₃ d = [d₁, d₂, d₃].count d) ∧
    (∀ k : ℕ, fiberSpectrumSchattenEvenData d₁ d₂ d₃ k = fiberSpectrumNegativePowerSum d₁ d₂ d₃ k) ∧
    cubicFromPowerSums
      (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 1)
      (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 2)
      (fiberSpectrumNegativePowerSum d₁ d₂ d₃ 3) =
        reciprocalSpectrumPolynomial d₁ d₂ d₃

theorem paper_derived_fiber_single_stieltjes_histogram_recovery :
    derivedFiberSingleStieltjesHistogramRecoveryStatement := by
  intro d₁ d₂ d₃ h₁ h₂ h₃
  have h :=
    paper_pom_fiber_spectrum_stieltjes_rigidity_determinant_schatten d₁ d₂ d₃ h₁ h₂ h₃
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end Omega.POM
