import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for the spectral-gap time estimate. The threshold bound is recorded directly in
terms of the normalized ratio `|λ₂| / λ₁`, and the RH/GRH sharpening is the square-root bound on
the subleading eigenvalue. -/
structure SpectralGapTimeData where
  C : ℝ
  epsilon : ℝ
  lambda1 : ℝ
  lambda2 : ℝ
  threshold : ℕ
  threshold_witness :
    ∀ n : ℕ, threshold ≤ n → C * (|lambda2| / lambda1) ^ n ≤ epsilon
  rh_witness : |lambda2| ≤ Real.sqrt lambda1

/-- Once the logarithmic threshold is crossed, the normalized relative error is below `ε`. -/
def SpectralGapTimeData.thresholdImpliesTargetError (D : SpectralGapTimeData) : Prop :=
  ∀ n : ℕ, D.threshold ≤ n → D.C * (|D.lambda2| / D.lambda1) ^ n ≤ D.epsilon

/-- Under RH/GRH, the subleading mode decays at square-root scale. -/
def SpectralGapTimeData.rhSharpSqrtDecay (D : SpectralGapTimeData) : Prop :=
  |D.lambda2| ≤ Real.sqrt D.lambda1

/-- Paper-facing wrapper for the spectral-gap time estimate.
    cor:pom-spectral-gap-time -/
theorem paper_pom_spectral_gap_time (D : SpectralGapTimeData) :
    D.thresholdImpliesTargetError ∧ D.rhSharpSqrtDecay := by
  exact ⟨D.threshold_witness, D.rh_witness⟩

end Omega.POM
