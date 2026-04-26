import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Zeta.XiIntegratedDefectSumruleEndpointFlux

namespace Omega.Zeta

open Filter
open scoped BigOperators

noncomputable section

/-- Concrete data for the scalar integrated-defect certificate. Each off-critical contribution
is required to carry strictly positive integrated defect mass. -/
structure xi_scalar_certificate_integrated_defect_data where
  sumruleData : xi_integrated_defect_sumrule_endpoint_flux_data
  positiveContribution : ∀ i : Fin sumruleData.n, 0 < (sumruleData.summand i).defectIntegral

/-- RH certificate in the finite scalar model: there are no off-critical blocks. -/
def xi_scalar_certificate_integrated_defect_rh
    (D : xi_scalar_certificate_integrated_defect_data) : Prop :=
  D.sumruleData.n = 0

/-- Endpoint limit detected by the finite integrated-defect sumrule. -/
noncomputable def xi_scalar_certificate_integrated_defect_endpointLimit
    (D : xi_scalar_certificate_integrated_defect_data) : ℝ :=
  xi_integrated_defect_sumrule_endpoint_flux_closedFormSum D.sumruleData

/-- Paper label: `cor:xi-scalar-certificate-integrated-defect`. In the finite integrated-defect
model, RH is the absence of off-critical blocks, which is equivalent to vanishing endpoint limit;
if any off-critical block remains, its positive defect contribution forces a strictly positive
endpoint limit. -/
theorem paper_xi_scalar_certificate_integrated_defect
    (D : xi_scalar_certificate_integrated_defect_data) :
    (xi_scalar_certificate_integrated_defect_rh D ↔
      xi_scalar_certificate_integrated_defect_endpointLimit D = 0) ∧
    (¬ xi_scalar_certificate_integrated_defect_rh D →
      0 < xi_scalar_certificate_integrated_defect_endpointLimit D) ∧
    Tendsto (xi_integrated_defect_sumrule_endpoint_flux_endpointFlux D.sumruleData) atTop
      (nhds (xi_scalar_certificate_integrated_defect_endpointLimit D)) := by
  have hsumrule := paper_xi_integrated_defect_sumrule_endpoint_flux D.sumruleData
  have hpositive_limit :
      ¬ xi_scalar_certificate_integrated_defect_rh D →
        0 < xi_scalar_certificate_integrated_defect_endpointLimit D := by
    intro hnotRh
    have hn_ne : D.sumruleData.n ≠ 0 := by
      simpa [xi_scalar_certificate_integrated_defect_rh] using hnotRh
    have hn_pos : 0 < D.sumruleData.n := Nat.pos_iff_ne_zero.mpr hn_ne
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k < D.sumruleData.n := ⟨0, hn_pos⟩
    let i : Fin D.sumruleData.n := ⟨k, hk⟩
    have hterm_nonneg :
        ∀ j : Fin D.sumruleData.n,
          0 ≤ xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand D.sumruleData j := by
      intro j
      have hEq :
          (D.sumruleData.summand j).defectIntegral =
            xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand D.sumruleData j := by
        simpa [xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand] using
          (paper_xi_single_defect_integrated_closed_form (D.sumruleData.summand j)).2
      exact hEq ▸ le_of_lt (D.positiveContribution j)
    have hterm_pos :
        0 < xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand D.sumruleData i := by
      have hEq :
          (D.sumruleData.summand i).defectIntegral =
            xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand D.sumruleData i := by
        simpa [xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand] using
          (paper_xi_single_defect_integrated_closed_form (D.sumruleData.summand i)).2
      exact hEq ▸ D.positiveContribution i
    have hle :
        xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand D.sumruleData i ≤
          xi_scalar_certificate_integrated_defect_endpointLimit D := by
      unfold xi_scalar_certificate_integrated_defect_endpointLimit
      exact Finset.single_le_sum (fun j _ => hterm_nonneg j) (by simp)
    exact lt_of_lt_of_le hterm_pos hle
  refine ⟨?_, hpositive_limit, ?_⟩
  · constructor
    · intro hRh
      cases D with
      | mk sumruleData positiveContribution =>
          cases sumruleData with
          | mk n center summand =>
              have hn : n = 0 := by
                simpa [xi_scalar_certificate_integrated_defect_rh] using hRh
              subst n
              simp [xi_scalar_certificate_integrated_defect_rh,
                xi_scalar_certificate_integrated_defect_endpointLimit,
                xi_integrated_defect_sumrule_endpoint_flux_closedFormSum] at hRh ⊢
    · intro hzero
      by_contra hnotRh
      have hpos :
          0 < xi_scalar_certificate_integrated_defect_endpointLimit D := hpositive_limit hnotRh
      exact (ne_of_gt hpos) hzero
  · simpa [xi_scalar_certificate_integrated_defect_endpointLimit] using hsumrule.2.2

end

end Omega.Zeta
