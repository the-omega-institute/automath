import Mathlib.Tactic
import Omega.Zeta.XiComovingJensenDefectKernelDecomposition
import Omega.Zeta.XiLimitDefectPotentialL1Sumrule
import Omega.Zeta.XiSingleDefectIntegratedClosedForm

namespace Omega.Zeta

open MeasureTheory Real
open scoped BigOperators

noncomputable section

/-- Finite package of translated single-defect blocks used for the integrated sumrule. -/
structure xi_integrated_defect_sumrule_endpoint_flux_data where
  n : ℕ
  center : Fin n → ℝ
  summand : Fin n → XiSingleDefectIntegratedClosedFormData

/-- Concrete zero package obtained by placing each single-defect block at its center. -/
def xi_integrated_defect_sumrule_endpoint_flux_zeroData
    (D : xi_integrated_defect_sumrule_endpoint_flux_data) :
    xi_comoving_jensen_defect_kernel_decomposition_zero_data where
  Zero := Fin D.n
  gamma := D.center
  delta := fun i => (D.summand i).δ
  delta_pos := fun i => (D.summand i).hδ.1
  delta_le_one := fun i => le_of_lt (D.summand i).hδ.2
  bounded_height_finite := by
    intro x0 R
    classical
    exact Set.toFinite _

/-- Closed-form contribution of a single integrated defect block. -/
def xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand
    (D : xi_integrated_defect_sumrule_endpoint_flux_data) (i : Fin D.n) : ℝ :=
  2 * (1 + (D.summand i).δ) *
      Real.arctan
        (singleDefectSupportRadius (D.summand i).ρ (D.summand i).δ / (1 + (D.summand i).δ)) -
    2 * (1 - (D.summand i).δ) *
      Real.arctan
        (singleDefectSupportRadius (D.summand i).ρ (D.summand i).δ / (1 - (D.summand i).δ))

/-- The total closed-form sum over all single defects. -/
def xi_integrated_defect_sumrule_endpoint_flux_closedFormSum
    (D : xi_integrated_defect_sumrule_endpoint_flux_data) : ℝ :=
  ∑ i, xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand D i

/-- Weight package for the finite translated defect-potential sum rule. -/
def xi_integrated_defect_sumrule_endpoint_flux_limitData
    (D : xi_integrated_defect_sumrule_endpoint_flux_data) :
    XiLimitDefectPotentialL1SumruleData where
  n := D.n
  center := D.center
  weight := fun i => (D.summand i).defectIntegral / (2 * Real.pi)

/-- The integrated defect obtained from the finite translated potential. -/
def xi_integrated_defect_sumrule_endpoint_flux_integratedDefect
    (D : xi_integrated_defect_sumrule_endpoint_flux_data) : ℝ :=
  ∫ x, (xi_integrated_defect_sumrule_endpoint_flux_limitData D).defectPotential x

/-- Constant endpoint-flux profile saturated by the exact finite sumrule. -/
def xi_integrated_defect_sumrule_endpoint_flux_endpointFlux
    (D : xi_integrated_defect_sumrule_endpoint_flux_data) : ℕ → ℝ :=
  fun _ => xi_integrated_defect_sumrule_endpoint_flux_closedFormSum D

/-- Publication-facing package: the kernel decomposition specializes to the translated single
defects, the integrated defect equals the exact closed-form sum, and the endpoint flux converges
to the same limit. -/
def xi_integrated_defect_sumrule_endpoint_flux_statement
    (D : xi_integrated_defect_sumrule_endpoint_flux_data) : Prop :=
  (∀ z : Fin D.n,
    xi_comoving_jensen_defect_kernel_decomposition_disk_zero_contribution
        1 ((xi_integrated_defect_sumrule_endpoint_flux_zeroData D).gamma z)
        ((xi_integrated_defect_sumrule_endpoint_flux_zeroData D).delta z) =
      xi_comoving_jensen_defect_kernel_decomposition_kernel
        1 ((xi_integrated_defect_sumrule_endpoint_flux_zeroData D).delta z)
        ((xi_integrated_defect_sumrule_endpoint_flux_zeroData D).gamma z)) ∧
    xi_integrated_defect_sumrule_endpoint_flux_integratedDefect D =
      xi_integrated_defect_sumrule_endpoint_flux_closedFormSum D ∧
    Filter.Tendsto (xi_integrated_defect_sumrule_endpoint_flux_endpointFlux D)
      Filter.atTop
      (nhds (xi_integrated_defect_sumrule_endpoint_flux_closedFormSum D))

/-- Paper label: `thm:xi-integrated-defect-sumrule-endpoint-flux`. -/
theorem paper_xi_integrated_defect_sumrule_endpoint_flux
    (D : xi_integrated_defect_sumrule_endpoint_flux_data) :
    xi_integrated_defect_sumrule_endpoint_flux_statement D := by
  have hdecomp :=
    paper_xi_comoving_jensen_defect_kernel_decomposition
      (xi_integrated_defect_sumrule_endpoint_flux_zeroData D) 0 1
  have hsumrule :=
    paper_xi_limit_defect_potential_l1_sumrule
      (xi_integrated_defect_sumrule_endpoint_flux_limitData D)
  have hpi_ne : (2 * Real.pi : ℝ) ≠ 0 := by
    nlinarith [Real.pi_pos]
  refine ⟨?_, ?_, ?_⟩
  · intro z
    simpa [xi_integrated_defect_sumrule_endpoint_flux_zeroData] using hdecomp.1 z
  · have hintegral :
        xi_integrated_defect_sumrule_endpoint_flux_integratedDefect D =
          ∑ i, (D.summand i).defectIntegral := by
      calc
        xi_integrated_defect_sumrule_endpoint_flux_integratedDefect D
            = 2 * Real.pi *
                (xi_integrated_defect_sumrule_endpoint_flux_limitData D).weightedSum := by
                  simpa [xi_integrated_defect_sumrule_endpoint_flux_integratedDefect,
                    XiLimitDefectPotentialL1SumruleData.integral_eq_two_pi_weighted_sum] using
                    hsumrule.2
        _ = 2 * Real.pi * ∑ i, (D.summand i).defectIntegral / (2 * Real.pi) := by
              rfl
        _ = ∑ i, 2 * Real.pi * ((D.summand i).defectIntegral / (2 * Real.pi)) := by
              rw [Finset.mul_sum]
        _ = ∑ i, (D.summand i).defectIntegral := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              field_simp [hpi_ne]
    calc
      xi_integrated_defect_sumrule_endpoint_flux_integratedDefect D
          = ∑ i, (D.summand i).defectIntegral := hintegral
      _ = ∑ i, xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand D i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa [xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand] using
              (paper_xi_single_defect_integrated_closed_form (D.summand i)).2
      _ = xi_integrated_defect_sumrule_endpoint_flux_closedFormSum D := by
            rfl
  · simpa [xi_integrated_defect_sumrule_endpoint_flux_endpointFlux] using tendsto_const_nhds

end

end Omega.Zeta
