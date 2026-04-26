import Mathlib.Tactic
import Omega.Zeta.XiOffcriticalCountBoundByIntegratedDefect

namespace Omega.Zeta

/-- The single-radius threshold profile `J_ρ(δ)` used in the integrated-defect exclusion test. -/
noncomputable def xi_integrated_defect_single_radius_exclusion_band_threshold
    (rho delta : ℝ) : ℝ :=
  xi_offcritical_count_bound_by_integrated_defect_singleMass rho delta

/-- Concrete data for the single-radius integrated-defect exclusion criterion. -/
structure XiIntegratedDefectSingleRadiusExclusionBandData where
  rho : ℝ
  Delta : ℝ
  integratedDefect : ℝ
  hrho : 0 < rho ∧ rho < 1
  hDelta : 0 < Delta
  hStrict :
    integratedDefect <
      xi_integrated_defect_single_radius_exclusion_band_threshold rho Delta
  hMonotone :
    ∀ {delta : ℝ}, Delta ≤ delta →
      xi_integrated_defect_single_radius_exclusion_band_threshold rho Delta ≤
        xi_integrated_defect_single_radius_exclusion_band_threshold rho delta

/-- Publication-facing exclusion statement: no defect level at least `Δ` can remain compatible with
the recorded strict integrated-defect bound. -/
def XiIntegratedDefectSingleRadiusExclusionBandData.statement
    (D : XiIntegratedDefectSingleRadiusExclusionBandData) : Prop :=
  ¬ ∃ delta : ℝ,
      D.Delta ≤ delta ∧
        xi_integrated_defect_single_radius_exclusion_band_threshold D.rho delta ≤
          D.integratedDefect

/-- Paper label: `cor:xi-integrated-defect-single-radius-exclusion-band`. -/
theorem paper_xi_integrated_defect_single_radius_exclusion_band
    (D : XiIntegratedDefectSingleRadiusExclusionBandData) : D.statement := by
  rintro ⟨delta, hdelta, hdeltaBound⟩
  have hmono :
      xi_integrated_defect_single_radius_exclusion_band_threshold D.rho D.Delta ≤
        xi_integrated_defect_single_radius_exclusion_band_threshold D.rho delta :=
    D.hMonotone hdelta
  have hlt :
      D.integratedDefect <
        xi_integrated_defect_single_radius_exclusion_band_threshold D.rho delta :=
    lt_of_lt_of_le D.hStrict hmono
  exact not_le_of_gt hlt hdeltaBound

end Omega.Zeta
