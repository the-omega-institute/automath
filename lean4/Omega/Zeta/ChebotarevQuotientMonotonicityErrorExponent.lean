import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete quotient/inflation package for Chebotarev error-exponent monotonicity.
Every nontrivial quotient channel has an inflated ambient channel with the same spectral radius;
the ambient channel bound controls `etaG`, while the cofactor radii are the corresponding
reciprocals. -/
structure xi_time_part64ab_quotient_monotonicity_error_exponent_data where
  HChannel : Type*
  GChannel : Type*
  etaH : ℝ
  etaG : ℝ
  lambda1 : ℝ
  radiusG : ℝ
  radiusH : ℝ
  xi_time_part64ab_quotient_monotonicity_error_exponent_inflate :
    HChannel → GChannel
  xi_time_part64ab_quotient_monotonicity_error_exponent_spectralH :
    HChannel → ℝ
  xi_time_part64ab_quotient_monotonicity_error_exponent_spectralG :
    GChannel → ℝ
  xi_time_part64ab_quotient_monotonicity_error_exponent_same_spectral_radius :
    ∀ χ : HChannel,
      xi_time_part64ab_quotient_monotonicity_error_exponent_spectralH χ =
        xi_time_part64ab_quotient_monotonicity_error_exponent_spectralG
          (xi_time_part64ab_quotient_monotonicity_error_exponent_inflate χ)
  xi_time_part64ab_quotient_monotonicity_error_exponent_G_channel_bound :
    ∀ γ : GChannel,
      xi_time_part64ab_quotient_monotonicity_error_exponent_spectralG γ ≤ etaG
  xi_time_part64ab_quotient_monotonicity_error_exponent_etaH_le_of_channel_bound :
    (∀ χ : HChannel,
      xi_time_part64ab_quotient_monotonicity_error_exponent_spectralH χ ≤ etaG) →
      etaH ≤ etaG
  xi_time_part64ab_quotient_monotonicity_error_exponent_lambda1_nonneg :
    0 ≤ lambda1
  xi_time_part64ab_quotient_monotonicity_error_exponent_etaH_pos :
    0 < etaH
  xi_time_part64ab_quotient_monotonicity_error_exponent_radiusG_eq :
    radiusG = etaG⁻¹
  xi_time_part64ab_quotient_monotonicity_error_exponent_radiusH_eq :
    radiusH = etaH⁻¹

/-- Paper label: `thm:xi-time-part64ab-quotient-monotonicity-error-exponent`. -/
theorem paper_xi_time_part64ab_quotient_monotonicity_error_exponent
    (D : xi_time_part64ab_quotient_monotonicity_error_exponent_data) :
    D.etaH ≤ D.etaG ∧ D.etaH / D.lambda1 ≤ D.etaG / D.lambda1 ∧
      D.radiusG ≤ D.radiusH := by
  have heta : D.etaH ≤ D.etaG :=
    D.xi_time_part64ab_quotient_monotonicity_error_exponent_etaH_le_of_channel_bound
      (by
        intro χ
        rw [D.xi_time_part64ab_quotient_monotonicity_error_exponent_same_spectral_radius χ]
        exact
          D.xi_time_part64ab_quotient_monotonicity_error_exponent_G_channel_bound
            (D.xi_time_part64ab_quotient_monotonicity_error_exponent_inflate χ))
  refine ⟨heta, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right heta
      D.xi_time_part64ab_quotient_monotonicity_error_exponent_lambda1_nonneg
  · calc
      D.radiusG = D.etaG⁻¹ :=
        D.xi_time_part64ab_quotient_monotonicity_error_exponent_radiusG_eq
      _ ≤ D.etaH⁻¹ := by
        simpa [one_div] using
          one_div_le_one_div_of_le
            D.xi_time_part64ab_quotient_monotonicity_error_exponent_etaH_pos heta
      _ = D.radiusH :=
        D.xi_time_part64ab_quotient_monotonicity_error_exponent_radiusH_eq.symm

end Omega.Zeta
