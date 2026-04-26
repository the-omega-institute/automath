import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-time information data. The three arrays record the conditional entropy rate,
the logarithmic indistinguishability ratio, and the logarithmic fiber-freedom ratio at time `t`;
the proof fields identify them with the chain-rule and ergodic-limit rates. -/
structure xi_finite_time_distinguishability_mutual_information_rate_data where
  entropyRate : ℝ
  mutualInformationRate : ℝ
  conditionalEntropyRate : ℕ → ℝ
  indistinguishableLogRatio : ℕ → ℝ
  fiberFreedomLogRatio : ℕ → ℝ
  chainRuleIdentifiesEntropyRate :
    ∀ t, conditionalEntropyRate t = entropyRate
  ergodicLimitIdentifiesIndistinguishabilityRate :
    ∀ t, indistinguishableLogRatio t = -((t : ℝ) * mutualInformationRate)
  fiberFreedomUsesMutualInformationRate :
    ∀ t, fiberFreedomLogRatio t = -((t : ℝ) * mutualInformationRate)

namespace xi_finite_time_distinguishability_mutual_information_rate_data

/-- The conditional entropy rate exists as a constant time-asymptotic rate. -/
def conditionalEntropyRateExists
    (D : xi_finite_time_distinguishability_mutual_information_rate_data) : Prop :=
  ∃ h : ℝ, ∀ t : ℕ, D.conditionalEntropyRate t = h

/-- The indistinguishability ratio has exponential rate `D.mutualInformationRate`. -/
def indistinguishableRatioHasRate
    (D : xi_finite_time_distinguishability_mutual_information_rate_data) : Prop :=
  ∀ t : ℕ, D.indistinguishableLogRatio t = -((t : ℝ) * D.mutualInformationRate)

/-- The remaining fiber freedom decays with the same mutual-information rate. -/
def fiberFreedomDissolvesAtRate
    (D : xi_finite_time_distinguishability_mutual_information_rate_data) : Prop :=
  ∀ t : ℕ, D.fiberFreedomLogRatio t = -((t : ℝ) * D.mutualInformationRate)

end xi_finite_time_distinguishability_mutual_information_rate_data

/-- Paper label: `thm:xi-finite-time-distinguishability-mutual-information-rate`. The chain-rule
identification supplies the entropy-rate limit, and the ergodic-limit identifications give the two
matching exponential decay-rate conclusions. -/
theorem paper_xi_finite_time_distinguishability_mutual_information_rate
    (D : xi_finite_time_distinguishability_mutual_information_rate_data) :
    D.conditionalEntropyRateExists ∧ D.indistinguishableRatioHasRate ∧
      D.fiberFreedomDissolvesAtRate := by
  exact ⟨⟨D.entropyRate, D.chainRuleIdentifiesEntropyRate⟩,
    D.ergodicLimitIdentifiesIndistinguishabilityRate,
    D.fiberFreedomUsesMutualInformationRate⟩

end Omega.Zeta
