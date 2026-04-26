import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete package for the nonresonant twisted zeta prime-orbit estimate.  The spectral
radius inequality records that the Perron error radius is bounded by the advertised exponential
error radius. -/
structure gm_twisted_zeta_prime_orbit_data where
  gm_twisted_zeta_prime_orbit_character : ℤ
  gm_twisted_zeta_prime_orbit_prime_orbit_count : ℕ → ℝ
  gm_twisted_zeta_prime_orbit_main_term : ℕ → ℝ
  gm_twisted_zeta_prime_orbit_error_constant : ℝ
  gm_twisted_zeta_prime_orbit_spectral_radius : ℝ
  gm_twisted_zeta_prime_orbit_error_radius : ℝ
  gm_twisted_zeta_prime_orbit_nonresonance_gap : ℝ
  gm_twisted_zeta_prime_orbit_nonresonant :
    gm_twisted_zeta_prime_orbit_character ≠ 0
  gm_twisted_zeta_prime_orbit_nonresonance_gap_pos :
    0 < gm_twisted_zeta_prime_orbit_nonresonance_gap
  gm_twisted_zeta_prime_orbit_error_constant_nonneg :
    0 ≤ gm_twisted_zeta_prime_orbit_error_constant
  gm_twisted_zeta_prime_orbit_spectral_radius_nonneg :
    0 ≤ gm_twisted_zeta_prime_orbit_spectral_radius
  gm_twisted_zeta_prime_orbit_spectral_radius_ineq :
    gm_twisted_zeta_prime_orbit_spectral_radius ≤ gm_twisted_zeta_prime_orbit_error_radius
  gm_twisted_zeta_prime_orbit_perron_error_bound :
    ∀ n : ℕ,
      |gm_twisted_zeta_prime_orbit_prime_orbit_count n -
          gm_twisted_zeta_prime_orbit_main_term n| ≤
        gm_twisted_zeta_prime_orbit_error_constant *
          gm_twisted_zeta_prime_orbit_spectral_radius ^ n

/-- The centered prime-orbit error term. -/
def gm_twisted_zeta_prime_orbit_error
    (D : gm_twisted_zeta_prime_orbit_data) (n : ℕ) : ℝ :=
  D.gm_twisted_zeta_prime_orbit_prime_orbit_count n -
    D.gm_twisted_zeta_prime_orbit_main_term n

/-- Paper-facing statement: nonresonance supplies a positive gap, and the Perron estimate
inherits the advertised exponential error radius from the spectral-radius inequality. -/
def gm_twisted_zeta_prime_orbit_statement
    (D : gm_twisted_zeta_prime_orbit_data) : Prop :=
  D.gm_twisted_zeta_prime_orbit_character ≠ 0 ∧
    0 < D.gm_twisted_zeta_prime_orbit_nonresonance_gap ∧
    D.gm_twisted_zeta_prime_orbit_spectral_radius ≤
      D.gm_twisted_zeta_prime_orbit_error_radius ∧
    ∀ n : ℕ,
      |gm_twisted_zeta_prime_orbit_error D n| ≤
        D.gm_twisted_zeta_prime_orbit_error_constant *
          D.gm_twisted_zeta_prime_orbit_error_radius ^ n

/-- Paper label: `thm:gm-twisted-zeta-prime-orbit`. -/
theorem paper_gm_twisted_zeta_prime_orbit
    (D : gm_twisted_zeta_prime_orbit_data) : gm_twisted_zeta_prime_orbit_statement D := by
  refine ⟨D.gm_twisted_zeta_prime_orbit_nonresonant,
    D.gm_twisted_zeta_prime_orbit_nonresonance_gap_pos,
    D.gm_twisted_zeta_prime_orbit_spectral_radius_ineq, ?_⟩
  intro n
  have hpow :
      D.gm_twisted_zeta_prime_orbit_spectral_radius ^ n ≤
        D.gm_twisted_zeta_prime_orbit_error_radius ^ n :=
    pow_le_pow_left₀ D.gm_twisted_zeta_prime_orbit_spectral_radius_nonneg
      D.gm_twisted_zeta_prime_orbit_spectral_radius_ineq n
  have hscale :
      D.gm_twisted_zeta_prime_orbit_error_constant *
          D.gm_twisted_zeta_prime_orbit_spectral_radius ^ n ≤
        D.gm_twisted_zeta_prime_orbit_error_constant *
          D.gm_twisted_zeta_prime_orbit_error_radius ^ n :=
    mul_le_mul_of_nonneg_left hpow D.gm_twisted_zeta_prime_orbit_error_constant_nonneg
  exact le_trans (D.gm_twisted_zeta_prime_orbit_perron_error_bound n) hscale

end Omega.SyncKernelRealInput
