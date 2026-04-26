import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Omega.Zeta.XiSingleDefectIntegratedClosedForm

namespace Omega.Zeta

open MeasureTheory

/-- The visible support interval of the single-defect readout. -/
noncomputable def xi_single_defect_mass_log_derivative_support (ρ δ : ℝ) : Set ℝ :=
  Set.Icc (-singleDefectSupportRadius ρ δ) (singleDefectSupportRadius ρ δ)

/-- The logarithmic-radius mass model whose slope is the support length. -/
noncomputable def xi_single_defect_mass_log_derivative_mass (ρ δ : ℝ) : ℝ → ℝ :=
  fun logρ => logρ * (2 * singleDefectSupportRadius ρ δ)

/-- Paper label: `prop:xi-single-defect-mass-log-derivative`. In the concrete interval model, the
derivative with respect to the logarithmic radius is the visible support length, and the support
indicator integrates to the same quantity `2 X(ρ,δ)`. -/
theorem paper_xi_single_defect_mass_log_derivative (ρ δ : ℝ) :
    HasDerivAt (xi_single_defect_mass_log_derivative_mass ρ δ)
        (2 * singleDefectSupportRadius ρ δ) (Real.log ρ) ∧
      ∫ x,
          Set.indicator (xi_single_defect_mass_log_derivative_support ρ δ)
            (fun _ : ℝ => (1 : ℝ)) x =
        2 * singleDefectSupportRadius ρ δ := by
  constructor
  · simpa [xi_single_defect_mass_log_derivative_mass, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_id (x := Real.log ρ)).mul_const (2 * singleDefectSupportRadius ρ δ)
  · let X := singleDefectSupportRadius ρ δ
    have hX : 0 ≤ X := by
      simp [X, singleDefectSupportRadius]
    calc
      ∫ x,
          Set.indicator (xi_single_defect_mass_log_derivative_support ρ δ)
            (fun _ : ℝ => (1 : ℝ)) x
          = volume.real (Set.Icc (-X) X) := by
              simpa [xi_single_defect_mass_log_derivative_support, X] using
                (MeasureTheory.integral_indicator_const (μ := volume) (E := ℝ)
                  (e := (1 : ℝ)) (s_meas := measurableSet_Icc) (s := Set.Icc (-X) X))
      _ = ENNReal.toReal (volume (Set.Icc (-X) X)) := rfl
      _ = ENNReal.toReal (ENNReal.ofReal (X - (-X))) := by
            simp [Real.volume_Icc]
      _ = 2 * X := by
            have htwoX : 0 ≤ 2 * X := by positivity
            rw [show X - (-X) = 2 * X by ring]
            rw [ENNReal.toReal_ofReal htwoX]
      _ = 2 * singleDefectSupportRadius ρ δ := by rfl
