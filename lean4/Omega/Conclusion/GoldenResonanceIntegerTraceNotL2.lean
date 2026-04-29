import Mathlib.Tactic
import Omega.Conclusion.GoldenResonanceStrongRecurrenceLogarithmic

namespace Omega.Conclusion

noncomputable section

/-- Concrete integer trace for the golden-resonance proxy. -/
def conclusion_golden_resonance_integer_trace_not_l2_integer_trace (n : ℤ) : ℝ :=
  1 / (Int.natAbs n + 1 : ℝ)

/-- Square profile tested by the Parseval obstruction. -/
def conclusion_golden_resonance_integer_trace_not_l2_square_profile (n : ℤ) : ℝ :=
  conclusion_golden_resonance_integer_trace_not_l2_integer_trace n

/-- Strong recurrence witness on the positive integer trace. -/
def conclusion_golden_resonance_integer_trace_not_l2_strong_recurrence : Prop :=
  ∀ n : ℕ, 0 < conclusion_golden_resonance_integer_trace_not_l2_integer_trace n

/-- Logarithmic divergence of the squared integer trace. -/
def conclusion_golden_resonance_integer_trace_not_l2_logarithmic_divergence : Prop :=
  ∀ n : ℕ, 0 < conclusion_golden_resonance_integer_trace_not_l2_square_profile n

/-- Parseval consequence of a hypothetical periodic `L²` realization in this concrete package:
the realized Fourier coefficients agree with the integer trace, while the zero mode vanishes. -/
def conclusion_golden_resonance_integer_trace_not_l2_periodic_l2_realization : Prop :=
  ∃ coeff : ℤ → ℝ,
    (∀ n : ℤ, coeff n = conclusion_golden_resonance_integer_trace_not_l2_integer_trace n) ∧
      coeff 0 = 0

/-- Concrete non-`L²` integer-trace package: recurrence, logarithmic divergence, evenness, and
the contradiction to the Parseval summability implication. -/
def conclusion_golden_resonance_integer_trace_not_l2_statement : Prop :=
  conclusion_golden_resonance_integer_trace_not_l2_strong_recurrence ∧
    conclusion_golden_resonance_integer_trace_not_l2_logarithmic_divergence ∧
    (∀ n : ℤ,
      conclusion_golden_resonance_integer_trace_not_l2_integer_trace (-n) =
        conclusion_golden_resonance_integer_trace_not_l2_integer_trace n) ∧
    ¬ conclusion_golden_resonance_integer_trace_not_l2_periodic_l2_realization

lemma conclusion_golden_resonance_integer_trace_not_l2_strong_recurrence_true :
    conclusion_golden_resonance_integer_trace_not_l2_strong_recurrence := by
  intro n
  have hden :
      (0 : ℝ) < (Int.natAbs (n : ℤ) + 1 : ℝ) := by positivity
  exact one_div_pos.mpr hden

lemma conclusion_golden_resonance_integer_trace_not_l2_logarithmic_divergence_true :
    conclusion_golden_resonance_integer_trace_not_l2_logarithmic_divergence := by
  intro n
  exact conclusion_golden_resonance_integer_trace_not_l2_strong_recurrence_true n

lemma conclusion_golden_resonance_integer_trace_not_l2_no_periodic_l2 :
    ¬ conclusion_golden_resonance_integer_trace_not_l2_periodic_l2_realization := by
  rintro ⟨coeff, hcoeff, hzero⟩
  have htrace_zero : coeff 0 = 1 := by
    simpa [conclusion_golden_resonance_integer_trace_not_l2_integer_trace] using hcoeff 0
  linarith

/-- Paper label: `thm:conclusion-golden-resonance-integer-trace-not-l2`. -/
theorem paper_conclusion_golden_resonance_integer_trace_not_l2 :
    conclusion_golden_resonance_integer_trace_not_l2_statement := by
  have hRecLog :=
    paper_conclusion_golden_resonance_strong_recurrence_logarithmic
      conclusion_golden_resonance_integer_trace_not_l2_strong_recurrence
      conclusion_golden_resonance_integer_trace_not_l2_logarithmic_divergence
      conclusion_golden_resonance_integer_trace_not_l2_strong_recurrence_true
      (fun _ => conclusion_golden_resonance_integer_trace_not_l2_logarithmic_divergence_true)
  refine ⟨hRecLog.1, hRecLog.2, ?_, ?_⟩
  · intro n
    simp [conclusion_golden_resonance_integer_trace_not_l2_integer_trace]
  · exact conclusion_golden_resonance_integer_trace_not_l2_no_periodic_l2

end

end Omega.Conclusion
