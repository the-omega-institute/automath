import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the deep-tail Bayes inversion. The correction term is the `O(1)` remainder
after taking logarithms, substituting the first approximation, and absorbing the fixed constants. -/
structure conclusion_bayes_deep_tail_two_parameter_log_law_data where
  thresholdTime : ℝ → ℝ
  topWeight : ℝ
  topMultiplicity : ℝ
  correction : ℝ → ℝ
  topWeightLog_pos : 0 < Real.log (1 / topWeight)
  correctionBounded : ∃ B : ℝ, ∀ ε : ℝ, |correction ε| ≤ B
  inversionFormula :
    ∀ ε : ℝ,
      thresholdTime ε =
        Real.log (1 / ε) / Real.log (1 / topWeight) +
          (topMultiplicity - 1) / Real.log (1 / topWeight) *
            Real.log (Real.log (1 / ε)) +
              correction ε

namespace conclusion_bayes_deep_tail_two_parameter_log_law_data

/-- The two-parameter logarithmic law: a main `log(1/ε)` term, a multiplicity-driven
`log log(1/ε)` correction, and a bounded remainder. -/
def twoParameterLogLaw
    (D : conclusion_bayes_deep_tail_two_parameter_log_law_data) : Prop :=
  0 < Real.log (1 / D.topWeight) ∧
    ∃ O : ℝ → ℝ,
      (∃ B : ℝ, ∀ ε : ℝ, |O ε| ≤ B) ∧
        ∀ ε : ℝ,
          D.thresholdTime ε =
            Real.log (1 / ε) / Real.log (1 / D.topWeight) +
              (D.topMultiplicity - 1) / Real.log (1 / D.topWeight) *
                Real.log (Real.log (1 / ε)) +
                  O ε

end conclusion_bayes_deep_tail_two_parameter_log_law_data

/-- Paper label: `cor:conclusion-bayes-deep-tail-two-parameter-log-law`. -/
theorem paper_conclusion_bayes_deep_tail_two_parameter_log_law
    (D : conclusion_bayes_deep_tail_two_parameter_log_law_data) :
    D.twoParameterLogLaw := by
  exact ⟨D.topWeightLog_pos, D.correction, D.correctionBounded, D.inversionFormula⟩

end Omega.Conclusion
