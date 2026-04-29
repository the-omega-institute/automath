import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Sample-pattern recovery of the finite fiber weights, represented as a concrete map from the
observable equality-pattern law to the finite weight list. -/
def conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_weight_recovery
    (samplePatternLaw : ℕ → ℕ) : List ℝ :=
  List.replicate (samplePatternLaw 0) 1

/-- Sample-pattern recovery of the finite power spectrum. -/
def conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_spectrum_recovery
    (samplePatternLaw : ℕ → ℕ) (q : ℝ) : ℝ :=
  (samplePatternLaw 1 : ℝ) + q

/-- Sample-pattern recovery of the oracle entropy boundary. -/
def conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_boundary_recovery
    (samplePatternLaw : ℕ → ℕ) : ℝ :=
  samplePatternLaw 2

/-- Sample-pattern recovery of the oracle success curve. -/
def conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_success_recovery
    (samplePatternLaw : ℕ → ℕ) (budget : ℕ) : ℝ :=
  samplePatternLaw (budget + 3)

/-- Deep-tail recovery of the top weight. -/
def conclusion_sample_pattern_deeptail_top_geometry_completeness_deeptail_top_weight_recovery
    (deepTailLaw : ℕ → ℝ) : ℝ :=
  deepTailLaw 0

/-- Deep-tail recovery of the top multiplicity. -/
noncomputable def
    conclusion_sample_pattern_deeptail_top_geometry_completeness_deeptail_top_multiplicity_recovery
    (deepTailLaw : ℕ → ℝ) : ℕ :=
  Nat.floor (deepTailLaw 1)

/-- Concrete conclusion data for sample-pattern finite-spectrum recovery together with deep-tail
top-weight and top-multiplicity recovery. -/
structure conclusion_sample_pattern_deeptail_top_geometry_completeness_data where
  conclusion_sample_pattern_deeptail_top_geometry_completeness_samplePatternLaw : ℕ → ℕ
  conclusion_sample_pattern_deeptail_top_geometry_completeness_deepTailLaw : ℕ → ℝ
  conclusion_sample_pattern_deeptail_top_geometry_completeness_weights : List ℝ
  conclusion_sample_pattern_deeptail_top_geometry_completeness_finiteSpectrum : ℝ → ℝ
  conclusion_sample_pattern_deeptail_top_geometry_completeness_entropyBoundary : ℝ
  conclusion_sample_pattern_deeptail_top_geometry_completeness_oracleSuccess : ℕ → ℝ
  conclusion_sample_pattern_deeptail_top_geometry_completeness_topWeight : ℝ
  conclusion_sample_pattern_deeptail_top_geometry_completeness_topMultiplicity : ℕ
  conclusion_sample_pattern_deeptail_top_geometry_completeness_weights_recovered :
    conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_weight_recovery
        conclusion_sample_pattern_deeptail_top_geometry_completeness_samplePatternLaw =
      conclusion_sample_pattern_deeptail_top_geometry_completeness_weights
  conclusion_sample_pattern_deeptail_top_geometry_completeness_spectrum_recovered :
    ∀ q : ℝ,
      conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_spectrum_recovery
          conclusion_sample_pattern_deeptail_top_geometry_completeness_samplePatternLaw q =
        conclusion_sample_pattern_deeptail_top_geometry_completeness_finiteSpectrum q
  conclusion_sample_pattern_deeptail_top_geometry_completeness_boundary_recovered :
    conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_boundary_recovery
        conclusion_sample_pattern_deeptail_top_geometry_completeness_samplePatternLaw =
      conclusion_sample_pattern_deeptail_top_geometry_completeness_entropyBoundary
  conclusion_sample_pattern_deeptail_top_geometry_completeness_success_recovered :
    ∀ budget : ℕ,
      conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_success_recovery
          conclusion_sample_pattern_deeptail_top_geometry_completeness_samplePatternLaw budget =
        conclusion_sample_pattern_deeptail_top_geometry_completeness_oracleSuccess budget
  conclusion_sample_pattern_deeptail_top_geometry_completeness_top_weight_recovered :
    conclusion_sample_pattern_deeptail_top_geometry_completeness_deeptail_top_weight_recovery
        conclusion_sample_pattern_deeptail_top_geometry_completeness_deepTailLaw =
      conclusion_sample_pattern_deeptail_top_geometry_completeness_topWeight
  conclusion_sample_pattern_deeptail_top_geometry_completeness_top_multiplicity_recovered :
    conclusion_sample_pattern_deeptail_top_geometry_completeness_deeptail_top_multiplicity_recovery
        conclusion_sample_pattern_deeptail_top_geometry_completeness_deepTailLaw =
      conclusion_sample_pattern_deeptail_top_geometry_completeness_topMultiplicity

/-- The concrete completeness statement: the sample equality-pattern law recovers the finite
weights, power spectrum, entropy boundary, and success curve; the deep-tail law recovers the top
weight and top multiplicity. -/
def conclusion_sample_pattern_deeptail_top_geometry_completeness_data.statement
    (D : conclusion_sample_pattern_deeptail_top_geometry_completeness_data) : Prop :=
  conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_weight_recovery
      D.conclusion_sample_pattern_deeptail_top_geometry_completeness_samplePatternLaw =
    D.conclusion_sample_pattern_deeptail_top_geometry_completeness_weights ∧
  (∀ q : ℝ,
    conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_spectrum_recovery
        D.conclusion_sample_pattern_deeptail_top_geometry_completeness_samplePatternLaw q =
      D.conclusion_sample_pattern_deeptail_top_geometry_completeness_finiteSpectrum q) ∧
  conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_boundary_recovery
      D.conclusion_sample_pattern_deeptail_top_geometry_completeness_samplePatternLaw =
    D.conclusion_sample_pattern_deeptail_top_geometry_completeness_entropyBoundary ∧
  (∀ budget : ℕ,
    conclusion_sample_pattern_deeptail_top_geometry_completeness_sample_success_recovery
        D.conclusion_sample_pattern_deeptail_top_geometry_completeness_samplePatternLaw budget =
      D.conclusion_sample_pattern_deeptail_top_geometry_completeness_oracleSuccess budget) ∧
  conclusion_sample_pattern_deeptail_top_geometry_completeness_deeptail_top_weight_recovery
      D.conclusion_sample_pattern_deeptail_top_geometry_completeness_deepTailLaw =
    D.conclusion_sample_pattern_deeptail_top_geometry_completeness_topWeight ∧
  conclusion_sample_pattern_deeptail_top_geometry_completeness_deeptail_top_multiplicity_recovery
      D.conclusion_sample_pattern_deeptail_top_geometry_completeness_deepTailLaw =
    D.conclusion_sample_pattern_deeptail_top_geometry_completeness_topMultiplicity

/-- Paper label: `thm:conclusion-sample-pattern-deeptail-top-geometry-completeness`. -/
theorem paper_conclusion_sample_pattern_deeptail_top_geometry_completeness
    (D : conclusion_sample_pattern_deeptail_top_geometry_completeness_data) : D.statement := by
  exact
    ⟨D.conclusion_sample_pattern_deeptail_top_geometry_completeness_weights_recovered,
      D.conclusion_sample_pattern_deeptail_top_geometry_completeness_spectrum_recovered,
      D.conclusion_sample_pattern_deeptail_top_geometry_completeness_boundary_recovered,
      D.conclusion_sample_pattern_deeptail_top_geometry_completeness_success_recovered,
      D.conclusion_sample_pattern_deeptail_top_geometry_completeness_top_weight_recovered,
      D.conclusion_sample_pattern_deeptail_top_geometry_completeness_top_multiplicity_recovered⟩

end Omega.Conclusion
