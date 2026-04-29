import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the Stirling-Bernoulli peeling hierarchy.  The finite-prefix
operator `peeledLimit` is the limiting value after removing lower-order gauge
coefficients; `evenZeta` is recovered from the same coefficient through the recorded
Bernoulli-zeta factor. -/
structure xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_data where
  xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_gaugeCoefficient : ℕ → ℝ
  xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_peeledLimit : ℕ → ℝ
  xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_evenZeta : ℕ → ℝ
  xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_recoveryFactor : ℕ → ℝ
  xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_peeling_limit_eq :
    ∀ r : ℕ, 1 ≤ r →
      xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_peeledLimit r =
        xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_gaugeCoefficient r
  xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_bernoulli_zeta_identity :
    ∀ r : ℕ, 1 ≤ r →
      xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_evenZeta r =
        xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_recoveryFactor r *
          xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_gaugeCoefficient r

/-- The peeled finite-prefix limits recover the Stirling-Bernoulli coefficients. -/
def xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_data.peelingLimitsRecoverCoefficients
    (D : xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_data) : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_peeledLimit r =
      D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_gaugeCoefficient r

/-- The even zeta values are recovered from the peeled limits and the explicit factor. -/
def xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_data.evenZetaRecoveryFormula
    (D : xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_data) : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_evenZeta r =
      D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_recoveryFactor r *
        D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_peeledLimit r

/-- Paper label:
`thm:xi-time-part60aa-gauge-constant-explicit-even-zeta-recovery`. -/
theorem paper_xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery
    (D : xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_data) :
    D.peelingLimitsRecoverCoefficients ∧ D.evenZetaRecoveryFormula := by
  constructor
  · intro r hr
    exact D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_peeling_limit_eq r hr
  · intro r hr
    calc
      D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_evenZeta r =
          D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_recoveryFactor r *
            D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_gaugeCoefficient r :=
        D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_bernoulli_zeta_identity r
          hr
      _ =
          D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_recoveryFactor r *
            D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_peeledLimit r := by
        rw [D.xi_time_part60aa_gauge_constant_explicit_even_zeta_recovery_peeling_limit_eq r hr]

end Omega.Zeta
