import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiLeyangTwoScaleCrossratioSlopeExponent

namespace Omega.Zeta

noncomputable section

/-- Concrete two-scale data for the Lee--Yang crossratio crossing drift calculation. -/
structure XiLeyangTwoScaleCrossratioCrossingDriftData where
  L : ℝ
  s : ℝ
  c : ℝ
  y₀ : ℝ
  hL : 1 < L
  hs : 1 < s
  hc : c ≠ 0
  hy₀ : y₀ ≠ 0
  slope : ℝ
  defect : ℝ
  hslope : slope ≠ 0

namespace XiLeyangTwoScaleCrossratioCrossingDriftData

/-- Leading-order drift extracted from the two-scale crossing equation. -/
noncomputable def xi_leyang_two_scale_crossratio_crossing_drift_crossingDrift
    (D : XiLeyangTwoScaleCrossratioCrossingDriftData) (scale : ℝ) : ℝ :=
  -D.defect / (D.slope * Real.log scale)

/-- Linearized crossing observable at scale `scale`. -/
noncomputable def xi_leyang_two_scale_crossratio_crossing_drift_crossingValue
    (D : XiLeyangTwoScaleCrossratioCrossingDriftData) (scale : ℝ) : ℝ :=
  D.y₀ *
    (1 + D.slope * D.xi_leyang_two_scale_crossratio_crossing_drift_crossingDrift scale +
      D.defect / Real.log scale)

/-- Linearized crossing equation near the critical point. -/
def xi_leyang_two_scale_crossratio_crossing_drift_crossingEquation
    (D : XiLeyangTwoScaleCrossratioCrossingDriftData) (scale δ : ℝ) : Prop :=
  xiLeyangTwoScaleCrossratio D.y₀
      (D.y₀ * (1 + D.slope * δ + D.defect / Real.log scale)) = 1

/-- The crossing point solves the linearized equation at both scales, the difference of the two
solutions has the expected `1 / log` drift form, and the ratio remains scale-invariant under the
common rescaling packaged by the earlier wrapper. -/
def crossingDriftEstimate (D : XiLeyangTwoScaleCrossratioCrossingDriftData) : Prop :=
  D.xi_leyang_two_scale_crossratio_crossing_drift_crossingEquation D.L
      (D.xi_leyang_two_scale_crossratio_crossing_drift_crossingDrift D.L) ∧
    D.xi_leyang_two_scale_crossratio_crossing_drift_crossingEquation (D.s * D.L)
      (D.xi_leyang_two_scale_crossratio_crossing_drift_crossingDrift (D.s * D.L)) ∧
    D.xi_leyang_two_scale_crossratio_crossing_drift_crossingDrift (D.s * D.L) -
        D.xi_leyang_two_scale_crossratio_crossing_drift_crossingDrift D.L =
      (-D.defect / D.slope) * (1 / Real.log (D.s * D.L) - 1 / Real.log D.L) ∧
    xiLeyangTwoScaleCrossratio (D.c * D.y₀)
        (D.c * D.xi_leyang_two_scale_crossratio_crossing_drift_crossingValue D.L) =
      xiLeyangTwoScaleCrossratio D.y₀
        (D.xi_leyang_two_scale_crossratio_crossing_drift_crossingValue D.L)

lemma xi_leyang_two_scale_crossratio_crossing_drift_log_ne_zero
    (D : XiLeyangTwoScaleCrossratioCrossingDriftData) {scale : ℝ} (hscale : 1 < scale) :
    Real.log scale ≠ 0 := by
  have hlog : 0 < Real.log scale := Real.log_pos hscale
  linarith

lemma xi_leyang_two_scale_crossratio_crossing_drift_crossingEquation_of_gt_one
    (D : XiLeyangTwoScaleCrossratioCrossingDriftData) {scale : ℝ} (hscale : 1 < scale) :
    D.xi_leyang_two_scale_crossratio_crossing_drift_crossingEquation scale
      (D.xi_leyang_two_scale_crossratio_crossing_drift_crossingDrift scale) := by
  have hlog : Real.log scale ≠ 0 :=
    D.xi_leyang_two_scale_crossratio_crossing_drift_log_ne_zero hscale
  have hbracket :
      1 + D.slope * D.xi_leyang_two_scale_crossratio_crossing_drift_crossingDrift scale +
          D.defect / Real.log scale = 1 := by
    unfold xi_leyang_two_scale_crossratio_crossing_drift_crossingDrift
    field_simp [D.hslope, hlog]
    ring
  unfold xi_leyang_two_scale_crossratio_crossing_drift_crossingEquation
  rw [hbracket]
  unfold xiLeyangTwoScaleCrossratio
  field_simp [D.hy₀]

lemma xi_leyang_two_scale_crossratio_crossing_drift_mul_gt_one
    (D : XiLeyangTwoScaleCrossratioCrossingDriftData) : 1 < D.s * D.L := by
  nlinarith [D.hL, D.hs]

end XiLeyangTwoScaleCrossratioCrossingDriftData

open XiLeyangTwoScaleCrossratioCrossingDriftData

/-- Paper label: `cor:xi-leyang-two-scale-crossratio-crossing-drift`. The linearized crossing
equation at scales `L` and `sL` solves to the explicit `1 / log` drift, and the earlier
crossratio wrapper keeps the ratio invariant under common rescaling. -/
theorem paper_xi_leyang_two_scale_crossratio_crossing_drift
    (D : XiLeyangTwoScaleCrossratioCrossingDriftData) : D.crossingDriftEstimate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact D.xi_leyang_two_scale_crossratio_crossing_drift_crossingEquation_of_gt_one D.hL
  · exact D.xi_leyang_two_scale_crossratio_crossing_drift_crossingEquation_of_gt_one
      D.xi_leyang_two_scale_crossratio_crossing_drift_mul_gt_one
  · have hLlog : Real.log D.L ≠ 0 :=
      D.xi_leyang_two_scale_crossratio_crossing_drift_log_ne_zero D.hL
    have hsLlog : Real.log (D.s * D.L) ≠ 0 :=
      D.xi_leyang_two_scale_crossratio_crossing_drift_log_ne_zero
        D.xi_leyang_two_scale_crossratio_crossing_drift_mul_gt_one
    unfold xi_leyang_two_scale_crossratio_crossing_drift_crossingDrift
    field_simp [D.hslope, hLlog, hsLlog]
    ring
  · have hwrapped :=
      paper_xi_leyang_two_scale_crossratio_invariant
        (crossratioConstruction :=
          xiLeyangTwoScaleCrossratio D.y₀
              (D.xi_leyang_two_scale_crossratio_crossing_drift_crossingValue D.L) =
            D.xi_leyang_two_scale_crossratio_crossing_drift_crossingValue D.L / D.y₀)
        (scalingLaw :=
          xiLeyangTwoScaleCrossratio (D.c * D.y₀)
              (D.c * D.xi_leyang_two_scale_crossratio_crossing_drift_crossingValue D.L) =
            xiLeyangTwoScaleCrossratio D.y₀
              (D.xi_leyang_two_scale_crossratio_crossing_drift_crossingValue D.L))
        (criticalSpecialization := True)
        (mixingInvariance := True)
        (hScaling := fun _ =>
          xiLeyangTwoScaleCrossratio_scale_invariant D.c D.y₀
            (D.xi_leyang_two_scale_crossratio_crossing_drift_crossingValue D.L) D.hc D.hy₀)
        (hCritical := fun _ => trivial)
        (hInvariant := fun _ => trivial) (by
          unfold xiLeyangTwoScaleCrossratio
          rfl)
    exact hwrapped.1

end

end Omega.Zeta
