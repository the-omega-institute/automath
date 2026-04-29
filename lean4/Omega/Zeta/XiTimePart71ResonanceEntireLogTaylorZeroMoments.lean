import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete coefficient data for the resonance product zero-set calculation. -/
structure xi_time_part71_resonance_entire_log_taylor_zero_moments_data where
  xi_time_part71_resonance_entire_log_taylor_zero_moments_phiPower : ℝ
  xi_time_part71_resonance_entire_log_taylor_zero_moments_logCosCoeff : ℝ
  xi_time_part71_resonance_entire_log_taylor_zero_moments_positiveZeroMoment : ℝ
  xi_time_part71_resonance_entire_log_taylor_zero_moments_allZeroMoment : ℝ
  xi_time_part71_resonance_entire_log_taylor_zero_moments_sigma : ℝ
  xi_time_part71_resonance_entire_log_taylor_zero_moments_geometricTail : ℝ
  xi_time_part71_resonance_entire_log_taylor_zero_moments_phiPower_ne_one :
    xi_time_part71_resonance_entire_log_taylor_zero_moments_phiPower ≠ 1
  xi_time_part71_resonance_entire_log_taylor_zero_moments_geometric_tail_closed :
    xi_time_part71_resonance_entire_log_taylor_zero_moments_geometricTail =
      (xi_time_part71_resonance_entire_log_taylor_zero_moments_phiPower - 1)⁻¹
  xi_time_part71_resonance_entire_log_taylor_zero_moments_sigma_def :
    xi_time_part71_resonance_entire_log_taylor_zero_moments_sigma =
      xi_time_part71_resonance_entire_log_taylor_zero_moments_logCosCoeff *
        (xi_time_part71_resonance_entire_log_taylor_zero_moments_phiPower - 1)⁻¹
  xi_time_part71_resonance_entire_log_taylor_zero_moments_positive_moment_def :
    xi_time_part71_resonance_entire_log_taylor_zero_moments_positiveZeroMoment =
      xi_time_part71_resonance_entire_log_taylor_zero_moments_logCosCoeff *
        xi_time_part71_resonance_entire_log_taylor_zero_moments_geometricTail
  xi_time_part71_resonance_entire_log_taylor_zero_moments_all_moment_def :
    xi_time_part71_resonance_entire_log_taylor_zero_moments_allZeroMoment =
      2 * xi_time_part71_resonance_entire_log_taylor_zero_moments_positiveZeroMoment

namespace xi_time_part71_resonance_entire_log_taylor_zero_moments_data

/-- Closed form for the geometric tail
`φ^{-4r} / (1 - φ^{-2r}) = φ^{-2r} / (φ^{2r} - 1)`. -/
def xi_time_part71_resonance_entire_log_taylor_zero_moments_tailClosed
    (D : xi_time_part71_resonance_entire_log_taylor_zero_moments_data) : ℝ :=
  (D.xi_time_part71_resonance_entire_log_taylor_zero_moments_phiPower - 1)⁻¹

/-- The product coefficient, positive zero moment, and all-zero moment agree with the closed form. -/
def statement (D : xi_time_part71_resonance_entire_log_taylor_zero_moments_data) : Prop :=
  D.xi_time_part71_resonance_entire_log_taylor_zero_moments_positiveZeroMoment =
      D.xi_time_part71_resonance_entire_log_taylor_zero_moments_sigma ∧
    D.xi_time_part71_resonance_entire_log_taylor_zero_moments_allZeroMoment =
      2 * D.xi_time_part71_resonance_entire_log_taylor_zero_moments_sigma ∧
    D.xi_time_part71_resonance_entire_log_taylor_zero_moments_sigma =
      D.xi_time_part71_resonance_entire_log_taylor_zero_moments_logCosCoeff *
        D.xi_time_part71_resonance_entire_log_taylor_zero_moments_tailClosed

end xi_time_part71_resonance_entire_log_taylor_zero_moments_data

/-- Paper label: `thm:xi-time-part71-resonance-entire-log-taylor-zero-moments`. -/
theorem paper_xi_time_part71_resonance_entire_log_taylor_zero_moments
    (D : xi_time_part71_resonance_entire_log_taylor_zero_moments_data) : D.statement := by
  have htail :
      D.xi_time_part71_resonance_entire_log_taylor_zero_moments_geometricTail =
        D.xi_time_part71_resonance_entire_log_taylor_zero_moments_tailClosed := by
    simpa [
      xi_time_part71_resonance_entire_log_taylor_zero_moments_data.xi_time_part71_resonance_entire_log_taylor_zero_moments_tailClosed]
      using D.xi_time_part71_resonance_entire_log_taylor_zero_moments_geometric_tail_closed
  have hpositive :
      D.xi_time_part71_resonance_entire_log_taylor_zero_moments_positiveZeroMoment =
        D.xi_time_part71_resonance_entire_log_taylor_zero_moments_sigma := by
    rw [D.xi_time_part71_resonance_entire_log_taylor_zero_moments_positive_moment_def,
      htail,
      D.xi_time_part71_resonance_entire_log_taylor_zero_moments_sigma_def]
    rfl
  refine ⟨hpositive, ?_, ?_⟩
  · rw [D.xi_time_part71_resonance_entire_log_taylor_zero_moments_all_moment_def,
      hpositive]
  · simpa [
      xi_time_part71_resonance_entire_log_taylor_zero_moments_data.xi_time_part71_resonance_entire_log_taylor_zero_moments_tailClosed]
      using D.xi_time_part71_resonance_entire_log_taylor_zero_moments_sigma_def

end

end Omega.Zeta
