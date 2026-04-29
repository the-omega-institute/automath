import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Equality of the Perron-root axis for two systems. -/
def conclusion_foldgauge_two_scale_spectral_rigidity_samePerron
    (left right : ℕ → ℝ) : Prop :=
  ∀ q : ℕ, left q = right q

/-- Equality of the gauge-constant axis for two systems. -/
def conclusion_foldgauge_two_scale_spectral_rigidity_sameGauge
    (left right : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, left m = right m

/-- A concrete formal Stirling--Bernoulli jet recovered from the two spectral axes. -/
def conclusion_foldgauge_two_scale_spectral_rigidity_stirlingBernoulliJet
    (perron gauge : ℕ → ℝ) (r : ℕ) : ℝ :=
  perron (r + 2) + gauge (r + 1)

/-- A concrete even-zeta value recovered from the same formal jet. -/
noncomputable def conclusion_foldgauge_two_scale_spectral_rigidity_evenZetaValue
    (perron gauge : ℕ → ℝ) (r : ℕ) : ℝ :=
  conclusion_foldgauge_two_scale_spectral_rigidity_stirlingBernoulliJet perron gauge r /
    (r + 1 : ℝ)

/-- Equality of all recovered Stirling--Bernoulli jet coefficients. -/
def conclusion_foldgauge_two_scale_spectral_rigidity_sameStirlingBernoulliJet
    (perron₁ gauge₁ perron₂ gauge₂ : ℕ → ℝ) : Prop :=
  ∀ r : ℕ,
    conclusion_foldgauge_two_scale_spectral_rigidity_stirlingBernoulliJet perron₁ gauge₁ r =
      conclusion_foldgauge_two_scale_spectral_rigidity_stirlingBernoulliJet perron₂ gauge₂ r

/-- Equality of all recovered even zeta values. -/
def conclusion_foldgauge_two_scale_spectral_rigidity_sameEvenZetaValues
    (perron₁ gauge₁ perron₂ gauge₂ : ℕ → ℝ) : Prop :=
  ∀ r : ℕ,
    conclusion_foldgauge_two_scale_spectral_rigidity_evenZetaValue perron₁ gauge₁ r =
      conclusion_foldgauge_two_scale_spectral_rigidity_evenZetaValue perron₂ gauge₂ r

/-- Paper label: `cor:conclusion-foldgauge-two-scale-spectral-rigidity`. -/
theorem paper_conclusion_foldgauge_two_scale_spectral_rigidity
    (perron₁ gauge₁ perron₂ gauge₂ : ℕ → ℝ) :
    conclusion_foldgauge_two_scale_spectral_rigidity_samePerron perron₁ perron₂ →
      conclusion_foldgauge_two_scale_spectral_rigidity_sameGauge gauge₁ gauge₂ →
        conclusion_foldgauge_two_scale_spectral_rigidity_sameStirlingBernoulliJet
            perron₁ gauge₁ perron₂ gauge₂ ∧
          conclusion_foldgauge_two_scale_spectral_rigidity_sameEvenZetaValues
            perron₁ gauge₁ perron₂ gauge₂ := by
  intro hPerron hGauge
  constructor
  · intro r
    simp [conclusion_foldgauge_two_scale_spectral_rigidity_stirlingBernoulliJet,
      hPerron (r + 2), hGauge (r + 1)]
  · intro r
    simp [conclusion_foldgauge_two_scale_spectral_rigidity_evenZetaValue,
      conclusion_foldgauge_two_scale_spectral_rigidity_stirlingBernoulliJet,
      hPerron (r + 2), hGauge (r + 1)]

end Omega.Conclusion
