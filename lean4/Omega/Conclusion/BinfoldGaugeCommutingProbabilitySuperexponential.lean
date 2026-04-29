import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete certificate for combining the commuting-probability identity with the separately
audited gauge-volume and conjugacy-class asymptotic expansions. -/
structure conclusion_binfold_gauge_commuting_probability_superexponential_certificate where
  logGaugeVolume : ℕ → ℝ
  logConjugacyClassCount : ℕ → ℝ
  negativeLogCommutingProbability : ℕ → ℝ
  gaugeVolumeMain : ℕ → ℝ
  conjugacyClassMain : ℕ → ℝ
  gaugeVolumeRemainder : ℕ → ℝ
  conjugacyClassRemainder : ℕ → ℝ
  commutingProbabilityLogIdentity :
    ∀ m : ℕ,
      negativeLogCommutingProbability m = logGaugeVolume m - logConjugacyClassCount m
  gaugeVolumeExpansion :
    ∀ m : ℕ, logGaugeVolume m = gaugeVolumeMain m + gaugeVolumeRemainder m
  conjugacyClassExpansion :
    ∀ m : ℕ, logConjugacyClassCount m = conjugacyClassMain m + conjugacyClassRemainder m

/-- The combined expansion obtained by subtracting the conjugacy-class asymptotic from the
gauge-volume asymptotic in the identity `-log cp(G_m)=log |G_m|-log k(G_m)`. -/
def conclusion_binfold_gauge_commuting_probability_superexponential_combined
    (C : conclusion_binfold_gauge_commuting_probability_superexponential_certificate)
    (m : ℕ) : Prop :=
  C.negativeLogCommutingProbability m =
    (C.gaugeVolumeMain m - C.conjugacyClassMain m) +
      (C.gaugeVolumeRemainder m - C.conjugacyClassRemainder m)

/-- Concrete statement for the commuting-probability superexponential law: any finite certificate
with the commuting-probability identity and the two source expansions yields the subtracted
expansion. -/
def conclusion_binfold_gauge_commuting_probability_superexponential_statement : Prop :=
  ∀ C : conclusion_binfold_gauge_commuting_probability_superexponential_certificate,
    ∀ m : ℕ,
      conclusion_binfold_gauge_commuting_probability_superexponential_combined C m

/-- Paper label: `thm:conclusion-binfold-gauge-commuting-probability-superexponential`. -/
theorem paper_conclusion_binfold_gauge_commuting_probability_superexponential :
    conclusion_binfold_gauge_commuting_probability_superexponential_statement := by
  intro C m
  unfold conclusion_binfold_gauge_commuting_probability_superexponential_combined
  rw [C.commutingProbabilityLogIdentity m, C.gaugeVolumeExpansion m,
    C.conjugacyClassExpansion m]
  ring

end Omega.Conclusion
