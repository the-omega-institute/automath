import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

namespace Omega.Zeta

open Real

/-- The visible support half-length `X(ρ,δ)` from the single-defect Jensen kernel. -/
noncomputable def singleDefectSupportRadius (ρ δ : ℝ) : ℝ :=
  Real.sqrt <| max 0 <| (ρ ^ 2 * (1 + δ) ^ 2 - (1 - δ) ^ 2) / (1 - ρ ^ 2)

/-- Data extracted from the integration-by-parts computation for the single-defect kernel. -/
structure XiSingleDefectIntegratedClosedFormData where
  ρ : ℝ
  δ : ℝ
  defectIntegral : ℝ
  hρ : 0 < ρ ∧ ρ < 1
  hδ : 0 < δ ∧ δ < 1
  integralIntermediate :
    defectIntegral =
      2 * singleDefectSupportRadius ρ δ * Real.log ρ +
        singleDefectSupportRadius ρ δ *
          Real.log
            (((singleDefectSupportRadius ρ δ) ^ 2 + (1 + δ) ^ 2) /
              ((singleDefectSupportRadius ρ δ) ^ 2 + (1 - δ) ^ 2)) +
        2 * (1 + δ) * Real.arctan (singleDefectSupportRadius ρ δ / (1 + δ)) -
        2 * (1 - δ) * Real.arctan (singleDefectSupportRadius ρ δ / (1 - δ))
  endpointSaturation :
    (((singleDefectSupportRadius ρ δ) ^ 2 + (1 - δ) ^ 2) /
      ((singleDefectSupportRadius ρ δ) ^ 2 + (1 + δ) ^ 2)) = ρ ^ 2

/-- The integrated single-defect Jensen kernel collapses to the arctangent closed form once the
boundary point identity `|w_δ(X)| = ρ` is used to cancel the logarithmic endpoint terms.
    prop:xi-single-defect-integrated-closed-form -/
theorem paper_xi_single_defect_integrated_closed_form
    (D : XiSingleDefectIntegratedClosedFormData) :
    0 ≤ singleDefectSupportRadius D.ρ D.δ ∧
      D.defectIntegral =
        2 * (1 + D.δ) *
            Real.arctan (singleDefectSupportRadius D.ρ D.δ / (1 + D.δ)) -
          2 * (1 - D.δ) *
            Real.arctan (singleDefectSupportRadius D.ρ D.δ / (1 - D.δ)) := by
  let X := singleDefectSupportRadius D.ρ D.δ
  let A : ℝ := 1 + D.δ
  let B : ℝ := 1 - D.δ
  have hX_nonneg : 0 ≤ X := by
    simp [X, singleDefectSupportRadius]
  have hρpos : 0 < D.ρ := D.hρ.1
  have hApos : 0 < A := by
    dsimp [A]
    linarith [D.hδ.1]
  have hBpos : 0 < B := by
    dsimp [B]
    linarith [D.hδ.2]
  have hA_sq_pos : 0 < A ^ 2 := by positivity
  have hB_sq_pos : 0 < B ^ 2 := by positivity
  have hnum_pos : 0 < X ^ 2 + B ^ 2 := by positivity
  have hden_pos : 0 < X ^ 2 + A ^ 2 := by positivity
  have hρsq_pos : 0 < D.ρ ^ 2 := by positivity
  have hratio :
      (X ^ 2 + A ^ 2) / (X ^ 2 + B ^ 2) = 1 / D.ρ ^ 2 := by
    have hInv := congrArg Inv.inv <| by
      simpa [X, A, B] using D.endpointSaturation
    have hnum_ne : (X ^ 2 + B ^ 2 : ℝ) ≠ 0 := ne_of_gt hnum_pos
    have hden_ne : (X ^ 2 + A ^ 2 : ℝ) ≠ 0 := ne_of_gt hden_pos
    have hρsq_ne : (D.ρ ^ 2 : ℝ) ≠ 0 := ne_of_gt hρsq_pos
    simpa [one_div, div_eq_mul_inv, hnum_ne, hden_ne, hρsq_ne, mul_comm, mul_left_comm,
      mul_assoc] using hInv
  have hlog_ratio :
      Real.log ((X ^ 2 + A ^ 2) / (X ^ 2 + B ^ 2)) = -2 * Real.log D.ρ := by
    rw [hratio]
    calc
      Real.log (1 / D.ρ ^ 2) = Real.log ((D.ρ ^ 2)⁻¹) := by simp [one_div]
      _ = -Real.log (D.ρ ^ 2) := by rw [Real.log_inv]
      _ = -(Real.log (D.ρ * D.ρ)) := by
            congr 1
            ring_nf
      _ = -(Real.log D.ρ + Real.log D.ρ) := by
            rw [Real.log_mul hρpos.ne' hρpos.ne']
      _ = -2 * Real.log D.ρ := by ring
  have hcancel :
      2 * X * Real.log D.ρ + X * Real.log ((X ^ 2 + A ^ 2) / (X ^ 2 + B ^ 2)) = 0 := by
    rw [hlog_ratio]
    ring
  refine ⟨hX_nonneg, ?_⟩
  calc
    D.defectIntegral
        = 2 * X * Real.log D.ρ +
            X * Real.log ((X ^ 2 + A ^ 2) / (X ^ 2 + B ^ 2)) +
            2 * A * Real.arctan (X / A) -
            2 * B * Real.arctan (X / B) := by
              simpa [X, A, B] using D.integralIntermediate
    _ = 2 * A * Real.arctan (X / A) - 2 * B * Real.arctan (X / B) := by
          rw [hcancel]
          ring
    _ = 2 * (1 + D.δ) *
            Real.arctan (singleDefectSupportRadius D.ρ D.δ / (1 + D.δ)) -
          2 * (1 - D.δ) *
            Real.arctan (singleDefectSupportRadius D.ρ D.δ / (1 - D.δ)) := by
          simp [X, A, B]

end Omega.Zeta
