import Omega.Conclusion.OracleFixedHistogramNearExhaustiveQueryLowerBound
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete side-information model over a fixed realization class. -/
structure conclusion_oracle_complete_spectral_sideinfo_nohelp_data where
  conclusion_oracle_complete_spectral_sideinfo_nohelp_candidateCount : ℕ
  conclusion_oracle_complete_spectral_sideinfo_nohelp_answerCount : ℕ
  conclusion_oracle_complete_spectral_sideinfo_nohelp_queryBudget : ℕ
  conclusion_oracle_complete_spectral_sideinfo_nohelp_realizationClass : Finset ℕ := ∅
  conclusion_oracle_complete_spectral_sideinfo_nohelp_fixedHistogram : ℕ := 0
  conclusion_oracle_complete_spectral_sideinfo_nohelp_histogram : ℕ → ℕ := fun _ => 0
  conclusion_oracle_complete_spectral_sideinfo_nohelp_sideInfo : ℕ → ℕ := fun _ => 0
  conclusion_oracle_complete_spectral_sideinfo_nohelp_histogram_fixed :
    ∀ x ∈ conclusion_oracle_complete_spectral_sideinfo_nohelp_realizationClass,
      conclusion_oracle_complete_spectral_sideinfo_nohelp_histogram x =
        conclusion_oracle_complete_spectral_sideinfo_nohelp_fixedHistogram := by
    simp
  conclusion_oracle_complete_spectral_sideinfo_nohelp_sideInfo_factors :
    ∀ x y : ℕ,
      x ∈ conclusion_oracle_complete_spectral_sideinfo_nohelp_realizationClass →
      y ∈ conclusion_oracle_complete_spectral_sideinfo_nohelp_realizationClass →
      conclusion_oracle_complete_spectral_sideinfo_nohelp_histogram x =
        conclusion_oracle_complete_spectral_sideinfo_nohelp_histogram y →
      conclusion_oracle_complete_spectral_sideinfo_nohelp_sideInfo x =
        conclusion_oracle_complete_spectral_sideinfo_nohelp_sideInfo y := by
    simp
  conclusion_oracle_complete_spectral_sideinfo_nohelp_identifies :
    conclusion_oracle_fixedhistogram_nearexhaustive_query_lowerbound_identifies
      conclusion_oracle_complete_spectral_sideinfo_nohelp_candidateCount
      conclusion_oracle_complete_spectral_sideinfo_nohelp_answerCount
      conclusion_oracle_complete_spectral_sideinfo_nohelp_queryBudget

namespace conclusion_oracle_complete_spectral_sideinfo_nohelp_data

/-- The side information is constant on every fixed-histogram realization class. -/
def conclusion_oracle_complete_spectral_sideinfo_nohelp_sideinfo_constant (D :
    conclusion_oracle_complete_spectral_sideinfo_nohelp_data) : Prop :=
  ∀ x y : ℕ,
    x ∈ D.conclusion_oracle_complete_spectral_sideinfo_nohelp_realizationClass →
    y ∈ D.conclusion_oracle_complete_spectral_sideinfo_nohelp_realizationClass →
    D.conclusion_oracle_complete_spectral_sideinfo_nohelp_sideInfo x =
      D.conclusion_oracle_complete_spectral_sideinfo_nohelp_sideInfo y

/-- The fixed-histogram query lower bound remains unchanged after complete side information. -/
def conclusion_oracle_complete_spectral_sideinfo_nohelp_lower_bound_unchanged (D :
    conclusion_oracle_complete_spectral_sideinfo_nohelp_data) : Prop :=
  conclusion_oracle_fixedhistogram_nearexhaustive_query_lowerbound_lowerBound
      D.conclusion_oracle_complete_spectral_sideinfo_nohelp_candidateCount
      D.conclusion_oracle_complete_spectral_sideinfo_nohelp_answerCount ≤
    D.conclusion_oracle_complete_spectral_sideinfo_nohelp_queryBudget

end conclusion_oracle_complete_spectral_sideinfo_nohelp_data

/-- Paper label: `thm:conclusion-oracle-complete-spectral-sideinfo-nohelp`. -/
theorem paper_conclusion_oracle_complete_spectral_sideinfo_nohelp
    (D : conclusion_oracle_complete_spectral_sideinfo_nohelp_data) :
    D.conclusion_oracle_complete_spectral_sideinfo_nohelp_lower_bound_unchanged := by
  have conclusion_oracle_complete_spectral_sideinfo_nohelp_constant :
      D.conclusion_oracle_complete_spectral_sideinfo_nohelp_sideinfo_constant := by
    intro x y hx hy
    apply D.conclusion_oracle_complete_spectral_sideinfo_nohelp_sideInfo_factors x y hx hy
    rw [D.conclusion_oracle_complete_spectral_sideinfo_nohelp_histogram_fixed x hx,
      D.conclusion_oracle_complete_spectral_sideinfo_nohelp_histogram_fixed y hy]
  clear conclusion_oracle_complete_spectral_sideinfo_nohelp_constant
  exact paper_conclusion_oracle_fixedhistogram_nearexhaustive_query_lowerbound
    D.conclusion_oracle_complete_spectral_sideinfo_nohelp_candidateCount
    D.conclusion_oracle_complete_spectral_sideinfo_nohelp_answerCount
    D.conclusion_oracle_complete_spectral_sideinfo_nohelp_queryBudget
    D.conclusion_oracle_complete_spectral_sideinfo_nohelp_identifies

end Omega.Conclusion
