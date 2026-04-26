import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Paper label: `thm:xi-foldbin-gauge-volume-three-factor-product`. A second-order
Stirling log-volume identity exponentiates to the normalized Gaussian/fiber product once the
gauge volume and fiber geometry factors are positive. -/
theorem paper_xi_foldbin_gauge_volume_three_factor_product (m : ℕ) (Xcard : ℝ)
    (gaugeVolume kappa fiberGeom : ℝ) (hgauge : 0 < gaugeVolume)
    (hfiber : 0 < fiberGeom)
    (hlog : ∃ r, 0 ≤ r ∧ r ≤ Xcard / 12 ∧
      Real.log gaugeVolume =
        (2 : ℝ)^m * (kappa - 1) + (Xcard / 2) * Real.log (2 * Real.pi) +
          Real.log fiberGeom + r) :
    ∃ r, 0 ≤ r ∧ r ≤ Xcard / 12 ∧
      gaugeVolume =
        Real.exp ((2 : ℝ)^m * (kappa - 1)) * (2 * Real.pi) ^ (Xcard / 2) *
          fiberGeom * Real.exp r := by
  rcases hlog with ⟨r, hr_nonneg, hr_le, hlog_eq⟩
  refine ⟨r, hr_nonneg, hr_le, ?_⟩
  have hbase_pos : 0 < (2 * Real.pi : ℝ) := by positivity
  have hpow :
      Real.exp ((Xcard / 2) * Real.log (2 * Real.pi)) =
        (2 * Real.pi) ^ (Xcard / 2) := by
    rw [Real.rpow_def_of_pos hbase_pos]
    congr 1
    ring
  calc
    gaugeVolume = Real.exp (Real.log gaugeVolume) := by rw [Real.exp_log hgauge]
    _ =
        Real.exp ((2 : ℝ)^m * (kappa - 1)) *
          (2 * Real.pi) ^ (Xcard / 2) * fiberGeom * Real.exp r := by
      rw [hlog_eq]
      rw [show
        (2 : ℝ)^m * (kappa - 1) + (Xcard / 2) * Real.log (2 * Real.pi) +
            Real.log fiberGeom + r =
          ((2 : ℝ)^m * (kappa - 1) + (Xcard / 2) * Real.log (2 * Real.pi)) +
            (Real.log fiberGeom + r) by ring]
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hfiber, hpow]
      ring

end

end Omega.Zeta
