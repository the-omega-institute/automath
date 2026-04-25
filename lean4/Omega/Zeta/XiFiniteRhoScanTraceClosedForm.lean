import Omega.Zeta.XiFiniteRhoScanTraceClosedFormDepthOnly

namespace Omega.Zeta

noncomputable section

/-- Paper label: `prop:xi-finite-rho-scan-trace-closed-form`. The finite scan trace is the
sum of the single-defect closed forms, and recentering the horizontal locations leaves it
unchanged. -/
theorem paper_xi_finite_rho_scan_trace_closed_form
    (D : xi_finite_rho_scan_trace_closed_form_depth_only_data) :
    (∀ i : Fin D.n, xi_single_defect_threshold_saturation_statement (D.summand i)) ∧
      xi_finite_rho_scan_trace_closed_form_depth_only_integratedTrace D =
        xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSum D ∧
      (∀ center' : Fin D.n → ℝ,
        xi_finite_rho_scan_trace_closed_form_depth_only_integratedTrace
            (xi_finite_rho_scan_trace_closed_form_depth_only_recenter D center') =
          xi_finite_rho_scan_trace_closed_form_depth_only_closedFormSum D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact paper_xi_single_defect_threshold_saturation (D.summand i)
  · exact (paper_xi_finite_rho_scan_trace_closed_form_depth_only D).2.1
  · exact (paper_xi_finite_rho_scan_trace_closed_form_depth_only D).2.2

end

end Omega.Zeta
