import Mathlib.Tactic
import Omega.Zeta.XiIntegratedDefectSumruleEndpointFlux
import Omega.Zeta.XiSingleDefectThresholdSaturation

namespace Omega.Zeta

noncomputable section

/-- Finite scan-trace data at a common radius `ρ`, with arbitrary horizontal centers and a finite
family of single-defect depth parameters. -/
structure xi_finite_rho_scan_trace_closed_form_depth_only_data where
  n : ℕ
  ρ : ℝ
  center : Fin n → ℝ
  summand : Fin n → XiSingleDefectIntegratedClosedFormData
  rho_eq : ∀ i : Fin n, (summand i).ρ = ρ

/-- The finite translated-defect package obtained from the common-radius scan data. -/
def xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData
    (D : xi_finite_rho_scan_trace_closed_form_depth_only_data) :
    xi_integrated_defect_sumrule_endpoint_flux_data where
  n := D.n
  center := D.center
  summand := D.summand

/-- Recenter the same finite depth spectrum at new horizontal locations. -/
def xi_finite_rho_scan_trace_closed_form_depth_only_recenter
    (D : xi_finite_rho_scan_trace_closed_form_depth_only_data) (center' : Fin D.n → ℝ) :
    xi_finite_rho_scan_trace_closed_form_depth_only_data where
  n := D.n
  ρ := D.ρ
  center := center'
  summand := D.summand
  rho_eq := D.rho_eq

/-- Closed-form contribution of one depth parameter to the finite scan trace. -/
def xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSummand
    (D : xi_finite_rho_scan_trace_closed_form_depth_only_data) (i : Fin D.n) : ℝ :=
  2 * (1 + (D.summand i).δ) *
      Real.arctan (singleDefectSupportRadius D.ρ (D.summand i).δ / (1 + (D.summand i).δ)) -
    2 * (1 - (D.summand i).δ) *
      Real.arctan (singleDefectSupportRadius D.ρ (D.summand i).δ / (1 - (D.summand i).δ))

/-- The finite depth-only closed form obtained by summing the single-defect contributions. -/
def xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSum
    (D : xi_finite_rho_scan_trace_closed_form_depth_only_data) : ℝ :=
  ∑ i, xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSummand D i

/-- The whole-line scan trace attached to the finite translated defect family. -/
def xi_finite_rho_scan_trace_closed_form_depth_only_integratedTrace
    (D : xi_finite_rho_scan_trace_closed_form_depth_only_data) : ℝ :=
  xi_integrated_defect_sumrule_endpoint_flux_integratedDefect
    (xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData D)

/-- Paper label: `prop:xi-finite-rho-scan-trace-closed-form-depth-only`. Each summand satisfies
the single-defect threshold dichotomy at the common radius `ρ`; summing the resulting closed forms
gives the finite scan trace, and the whole-line integral is independent of the horizontal centers,
so only the depth spectrum remains. -/
theorem paper_xi_finite_rho_scan_trace_closed_form_depth_only
    (D : xi_finite_rho_scan_trace_closed_form_depth_only_data) :
    (∀ i : Fin D.n,
      let S := D.summand i
      (D.ρ ≤ (1 - S.δ) / (1 + S.δ) → S.defectIntegral = 0) ∧
        ((1 - S.δ) / (1 + S.δ) < D.ρ →
          0 < singleDefectSupportRadius D.ρ S.δ ∧
            S.defectIntegral =
              xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSummand D i)) ∧
      xi_finite_rho_scan_trace_closed_form_depth_only_integratedTrace D =
        xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSum D ∧
      ∀ center' : Fin D.n → ℝ,
        xi_finite_rho_scan_trace_closed_form_depth_only_integratedTrace
            (xi_finite_rho_scan_trace_closed_form_depth_only_recenter D center') =
          xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSum D := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hsat := paper_xi_single_defect_threshold_saturation (D.summand i)
    exact ⟨by simpa [D.rho_eq i] using hsat.1,
      by simpa [xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSummand, D.rho_eq i]
        using hsat.2.1⟩
  · have hsum :=
      (paper_xi_integrated_defect_sumrule_endpoint_flux
        (xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData D)).2.1
    have hclosed :
        xi_integrated_defect_sumrule_endpoint_flux_closedFormSum
            (xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData D) =
          xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSum D := by
      unfold xi_integrated_defect_sumrule_endpoint_flux_closedFormSum
        xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSum
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hρi : (D.summand i).ρ = D.ρ := D.rho_eq i
      simp [xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand,
        xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSummand,
        xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData, hρi]
    calc
      xi_finite_rho_scan_trace_closed_form_depth_only_integratedTrace D =
          xi_integrated_defect_sumrule_endpoint_flux_closedFormSum
            (xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData D) := by
            simpa [xi_finite_rho_scan_trace_closed_form_depth_only_integratedTrace,
              xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData] using hsum
      _ = xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSum D := hclosed
  · intro center'
    have hsum :=
      (paper_xi_integrated_defect_sumrule_endpoint_flux
        (xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData
          (xi_finite_rho_scan_trace_closed_form_depth_only_recenter D center'))).2.1
    have hclosed :
        xi_integrated_defect_sumrule_endpoint_flux_closedFormSum
            (xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData
              (xi_finite_rho_scan_trace_closed_form_depth_only_recenter D center')) =
          xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSum D := by
      unfold xi_integrated_defect_sumrule_endpoint_flux_closedFormSum
        xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSum
        xi_finite_rho_scan_trace_closed_form_depth_only_recenter
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hρi : (D.summand i).ρ = D.ρ := D.rho_eq i
      simp [xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand,
        xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSummand,
        xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData,
        xi_finite_rho_scan_trace_closed_form_depth_only_recenter, hρi]
    calc
      xi_finite_rho_scan_trace_closed_form_depth_only_integratedTrace
          (xi_finite_rho_scan_trace_closed_form_depth_only_recenter D center') =
          xi_integrated_defect_sumrule_endpoint_flux_closedFormSum
            (xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData
              (xi_finite_rho_scan_trace_closed_form_depth_only_recenter D center')) := by
            simpa [xi_finite_rho_scan_trace_closed_form_depth_only_integratedTrace,
              xi_finite_rho_scan_trace_closed_form_depth_only_sumruleData,
              xi_finite_rho_scan_trace_closed_form_depth_only_recenter] using hsum
      _ = xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSum D := hclosed

end

end Omega.Zeta
