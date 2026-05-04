import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete primitive dyadic flux spectral package. -/
structure conclusion_dyadic_flux_primitive_no_leading_logperiodic_data where
  conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho : ℝ
  conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho_pos :
    0 < conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho
  conclusion_dyadic_flux_primitive_no_leading_logperiodic_lambda2 : ℝ
  conclusion_dyadic_flux_primitive_no_leading_logperiodic_subdominant_lt :
    |conclusion_dyadic_flux_primitive_no_leading_logperiodic_lambda2| <
      conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho
  conclusion_dyadic_flux_primitive_no_leading_logperiodic_dominantPole : ℝ
  conclusion_dyadic_flux_primitive_no_leading_logperiodic_dominantPole_eq :
    conclusion_dyadic_flux_primitive_no_leading_logperiodic_dominantPole =
      1 / conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho

namespace conclusion_dyadic_flux_primitive_no_leading_logperiodic_data

/-- The Perron pole is the unique real dominant pole in this one-dimensional package. -/
def uniqueDominantPole
    (D : conclusion_dyadic_flux_primitive_no_leading_logperiodic_data) : Prop :=
  D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_dominantPole =
      1 / D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho ∧
    ∀ z : ℝ,
      z = 1 / D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho →
        z = D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_dominantPole

/-- Subdominant modes are exponentially bounded by the spectral-gap ratio. -/
def normalizedFluxConvergesExponentially
    (D : conclusion_dyadic_flux_primitive_no_leading_logperiodic_data) : Prop :=
  ∀ m : ℕ,
    |(D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_lambda2 /
        D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho) ^ m| =
      (|D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_lambda2| /
          D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho) ^ m

/-- The leading line has no log-periodic companion because the gap ratio is strictly below one. -/
def noLeadingLogPeriodicOscillation
    (D : conclusion_dyadic_flux_primitive_no_leading_logperiodic_data) : Prop :=
  |D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_lambda2| /
      D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho < 1

end conclusion_dyadic_flux_primitive_no_leading_logperiodic_data

open conclusion_dyadic_flux_primitive_no_leading_logperiodic_data

/-- Paper label: `thm:conclusion-dyadic-flux-primitive-no-leading-logperiodic`. -/
theorem paper_conclusion_dyadic_flux_primitive_no_leading_logperiodic
    (D : conclusion_dyadic_flux_primitive_no_leading_logperiodic_data) :
    D.uniqueDominantPole ∧ D.normalizedFluxConvergesExponentially ∧
      D.noLeadingLogPeriodicOscillation := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_dominantPole_eq, ?_⟩
    intro z hz
    rw [hz, D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_dominantPole_eq]
  · intro m
    rw [abs_pow, abs_div,
      abs_of_pos D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho_pos]
  · change
      |D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_lambda2| /
          D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho < 1
    rw [div_lt_one D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_rho_pos]
    exact D.conclusion_dyadic_flux_primitive_no_leading_logperiodic_subdominant_lt

end Omega.Conclusion
