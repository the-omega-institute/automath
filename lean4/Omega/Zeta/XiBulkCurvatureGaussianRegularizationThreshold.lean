import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete one-variable package for Gaussian regularization of the bulk-curvature multiplier. -/
structure xi_bulk_curvature_gaussian_regularization_threshold_data where
  xi_bulk_curvature_gaussian_regularization_threshold_sigma : ℝ
  xi_bulk_curvature_gaussian_regularization_threshold_noiseAmplitude : ℝ
  xi_bulk_curvature_gaussian_regularization_threshold_outputBudget : ℝ
  xi_bulk_curvature_gaussian_regularization_threshold_sigma_pos :
    0 < xi_bulk_curvature_gaussian_regularization_threshold_sigma

/-- The quadratic exponent controlling the regularized inverse multiplier. -/
noncomputable def xi_bulk_curvature_gaussian_regularization_threshold_data.gaussianExponent
    (D : xi_bulk_curvature_gaussian_regularization_threshold_data) (ξ : ℝ) : ℝ :=
  Real.pi ^ 2 / (2 * D.xi_bulk_curvature_gaussian_regularization_threshold_sigma ^ 2) -
    (D.xi_bulk_curvature_gaussian_regularization_threshold_sigma ^ 2 * |ξ| - Real.pi) ^ 2 /
      (2 * D.xi_bulk_curvature_gaussian_regularization_threshold_sigma ^ 2)

/-- The frequency at which the completed-square quadratic is maximized. -/
noncomputable def xi_bulk_curvature_gaussian_regularization_threshold_data.criticalFrequency
    (D : xi_bulk_curvature_gaussian_regularization_threshold_data) : ℝ :=
  Real.pi / D.xi_bulk_curvature_gaussian_regularization_threshold_sigma ^ 2

/-- The value of the quadratic exponent at the critical frequency. -/
noncomputable def xi_bulk_curvature_gaussian_regularization_threshold_data.criticalGain
    (D : xi_bulk_curvature_gaussian_regularization_threshold_data) : ℝ :=
  Real.pi ^ 2 / (2 * D.xi_bulk_curvature_gaussian_regularization_threshold_sigma ^ 2)

/-- Worst-case Fourier noise remains within the packaged output budget at the maximal gain. -/
noncomputable def xi_bulk_curvature_gaussian_regularization_threshold_data.noiseControlled
    (D : xi_bulk_curvature_gaussian_regularization_threshold_data) : Prop :=
  D.xi_bulk_curvature_gaussian_regularization_threshold_noiseAmplitude *
      Real.exp D.criticalGain ≤
    D.xi_bulk_curvature_gaussian_regularization_threshold_outputBudget

/-- The Gaussian multiplier has maximal quadratic exponent at the critical frequency, and the
noise-control inequality is exactly the resulting threshold. -/
noncomputable def xi_bulk_curvature_gaussian_regularization_threshold_data.thresholdSatisfied
    (D : xi_bulk_curvature_gaussian_regularization_threshold_data) : Prop :=
  D.noiseControlled ∧
    D.gaussianExponent D.criticalFrequency = D.criticalGain ∧
      ∀ ξ : ℝ, D.gaussianExponent ξ ≤ D.criticalGain

lemma xi_bulk_curvature_gaussian_regularization_threshold_criticalFrequency_nonneg
    (D : xi_bulk_curvature_gaussian_regularization_threshold_data) :
    0 ≤ D.criticalFrequency := by
  unfold xi_bulk_curvature_gaussian_regularization_threshold_data.criticalFrequency
  positivity

lemma xi_bulk_curvature_gaussian_regularization_threshold_exponent_at_critical
    (D : xi_bulk_curvature_gaussian_regularization_threshold_data) :
    D.gaussianExponent D.criticalFrequency = D.criticalGain := by
  have hsigma_ne :
      D.xi_bulk_curvature_gaussian_regularization_threshold_sigma ≠ 0 :=
    ne_of_gt D.xi_bulk_curvature_gaussian_regularization_threshold_sigma_pos
  have hsigma_sq_ne :
      D.xi_bulk_curvature_gaussian_regularization_threshold_sigma ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 hsigma_ne
  have hcrit_abs : |D.criticalFrequency| = D.criticalFrequency :=
    abs_of_nonneg
      (xi_bulk_curvature_gaussian_regularization_threshold_criticalFrequency_nonneg D)
  unfold xi_bulk_curvature_gaussian_regularization_threshold_data.gaussianExponent
    xi_bulk_curvature_gaussian_regularization_threshold_data.criticalFrequency
    xi_bulk_curvature_gaussian_regularization_threshold_data.criticalGain at *
  rw [hcrit_abs]
  field_simp [hsigma_sq_ne]
  ring

lemma xi_bulk_curvature_gaussian_regularization_threshold_exponent_le_critical
    (D : xi_bulk_curvature_gaussian_regularization_threshold_data) (ξ : ℝ) :
    D.gaussianExponent ξ ≤ D.criticalGain := by
  have hsigma_sq_pos :
      0 < D.xi_bulk_curvature_gaussian_regularization_threshold_sigma ^ 2 := by
    exact sq_pos_of_ne_zero
      (ne_of_gt D.xi_bulk_curvature_gaussian_regularization_threshold_sigma_pos)
  unfold xi_bulk_curvature_gaussian_regularization_threshold_data.gaussianExponent
    xi_bulk_curvature_gaussian_regularization_threshold_data.criticalGain
  have hden :
      0 ≤ 2 * D.xi_bulk_curvature_gaussian_regularization_threshold_sigma ^ 2 := by
    positivity
  have hdefect :
      0 ≤
        (D.xi_bulk_curvature_gaussian_regularization_threshold_sigma ^ 2 * |ξ| -
            Real.pi) ^ 2 /
          (2 * D.xi_bulk_curvature_gaussian_regularization_threshold_sigma ^ 2) :=
    div_nonneg (sq_nonneg _) hden
  linarith

/-- Paper label: `cor:xi-bulk-curvature-gaussian-regularization-threshold`. -/
theorem paper_xi_bulk_curvature_gaussian_regularization_threshold
    (D : xi_bulk_curvature_gaussian_regularization_threshold_data) :
    D.noiseControlled → D.thresholdSatisfied := by
  intro hnoise
  exact ⟨hnoise,
    xi_bulk_curvature_gaussian_regularization_threshold_exponent_at_critical D,
    xi_bulk_curvature_gaussian_regularization_threshold_exponent_le_critical D⟩

end Omega.Zeta
