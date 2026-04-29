import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Zeta.XiIntegratedDefectSumruleEndpointFlux

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The single-defect mass at radius `ρ` and offset `δ`. -/
noncomputable def xi_offcritical_count_bound_by_integrated_defect_singleMass
    (ρ δ : ℝ) : ℝ :=
  2 * (1 + δ) * Real.arctan (singleDefectSupportRadius ρ δ / (1 + δ)) -
    2 * (1 - δ) * Real.arctan (singleDefectSupportRadius ρ δ / (1 - δ))

/-- Concrete data for the finite offcritical counting bound extracted from the integrated defect
sumrule. The threshold lower bound is recorded as a concrete inequality for each summand. -/
structure xi_offcritical_count_bound_by_integrated_defect_data where
  ρ : ℝ
  δ0 : ℝ
  hρ : 0 < ρ ∧ ρ < 1
  hδ0 : 0 < δ0 ∧ δ0 < 1
  sumruleData : xi_integrated_defect_sumrule_endpoint_flux_data
  hCommonRadius : ∀ i : Fin sumruleData.n, (sumruleData.summand i).ρ = ρ
  hDefectNonneg : ∀ i : Fin sumruleData.n, 0 ≤ (sumruleData.summand i).defectIntegral
  hSingleMassPos : 0 < xi_offcritical_count_bound_by_integrated_defect_singleMass ρ δ0
  hSingleMassLower :
    ∀ i : Fin sumruleData.n,
      δ0 ≤ (sumruleData.summand i).δ →
        xi_offcritical_count_bound_by_integrated_defect_singleMass ρ δ0 ≤
          (sumruleData.summand i).defectIntegral

/-- The indices whose offsets are at least `δ₀`. -/
def xi_offcritical_count_bound_by_integrated_defect_activeSet
    (D : xi_offcritical_count_bound_by_integrated_defect_data) : Finset (Fin D.sumruleData.n) :=
  Finset.univ.filter fun i => D.δ0 ≤ (D.sumruleData.summand i).δ

/-- The number of offcritical defects whose offset is at least `δ₀`. -/
def xi_offcritical_count_bound_by_integrated_defect_count
    (D : xi_offcritical_count_bound_by_integrated_defect_data) : ℕ :=
  (xi_offcritical_count_bound_by_integrated_defect_activeSet D).card

/-- The integrated defect supplied by the finite sumrule. -/
noncomputable def xi_offcritical_count_bound_by_integrated_defect_integratedDefect
    (D : xi_offcritical_count_bound_by_integrated_defect_data) : ℝ :=
  xi_integrated_defect_sumrule_endpoint_flux_integratedDefect D.sumruleData

/-- The finite counting bound: every active zero contributes at least the threshold mass, so the
count is controlled by the total integrated defect. -/
def xi_offcritical_count_bound_by_integrated_defect_data.bound
    (D : xi_offcritical_count_bound_by_integrated_defect_data) : Prop :=
  (xi_offcritical_count_bound_by_integrated_defect_count D : ℝ) ≤
    xi_offcritical_count_bound_by_integrated_defect_integratedDefect D /
      xi_offcritical_count_bound_by_integrated_defect_singleMass D.ρ D.δ0

/-- Paper label: `cor:xi-offcritical-count-bound-by-integrated-defect`. -/
theorem paper_xi_offcritical_count_bound_by_integrated_defect
    (D : xi_offcritical_count_bound_by_integrated_defect_data) : D.bound := by
  have hsumrule := paper_xi_integrated_defect_sumrule_endpoint_flux D.sumruleData
  have hintegrated :
      xi_offcritical_count_bound_by_integrated_defect_integratedDefect D =
        ∑ i, (D.sumruleData.summand i).defectIntegral := by
    calc
      xi_offcritical_count_bound_by_integrated_defect_integratedDefect D
          = xi_integrated_defect_sumrule_endpoint_flux_closedFormSum D.sumruleData := by
              simpa [xi_offcritical_count_bound_by_integrated_defect_integratedDefect] using
                hsumrule.2.1
      _ = ∑ i, xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand D.sumruleData i := by
            rfl
      _ = ∑ i, (D.sumruleData.summand i).defectIntegral := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa [xi_integrated_defect_sumrule_endpoint_flux_closedFormSummand,
              xi_offcritical_count_bound_by_integrated_defect_singleMass] using
              (paper_xi_single_defect_integrated_closed_form (D.sumruleData.summand i)).2.symm
  have hterm :
      ∀ i : Fin D.sumruleData.n,
        (if D.δ0 ≤ (D.sumruleData.summand i).δ then
            xi_offcritical_count_bound_by_integrated_defect_singleMass D.ρ D.δ0
          else 0) ≤
          (D.sumruleData.summand i).defectIntegral := by
    intro i
    by_cases hi : D.δ0 ≤ (D.sumruleData.summand i).δ
    · simpa [hi] using D.hSingleMassLower i hi
    · simp [hi, D.hDefectNonneg i]
  have hcount_mass :
      (xi_offcritical_count_bound_by_integrated_defect_count D : ℝ) *
          xi_offcritical_count_bound_by_integrated_defect_singleMass D.ρ D.δ0 ≤
        ∑ i, (D.sumruleData.summand i).defectIntegral := by
    calc
      (xi_offcritical_count_bound_by_integrated_defect_count D : ℝ) *
          xi_offcritical_count_bound_by_integrated_defect_singleMass D.ρ D.δ0
          =
            ∑ i : Fin D.sumruleData.n,
              if D.δ0 ≤ (D.sumruleData.summand i).δ then
                xi_offcritical_count_bound_by_integrated_defect_singleMass D.ρ D.δ0
              else 0 := by
                calc
                  (xi_offcritical_count_bound_by_integrated_defect_count D : ℝ) *
                      xi_offcritical_count_bound_by_integrated_defect_singleMass D.ρ D.δ0
                      =
                        (↑(xi_offcritical_count_bound_by_integrated_defect_activeSet D).card : ℝ) *
                          xi_offcritical_count_bound_by_integrated_defect_singleMass D.ρ D.δ0 := by
                            rfl
                  _ =
                        Finset.sum (xi_offcritical_count_bound_by_integrated_defect_activeSet D)
                          (fun _i =>
                            xi_offcritical_count_bound_by_integrated_defect_singleMass D.ρ D.δ0) := by
                            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
                  _ =
                        ∑ i : Fin D.sumruleData.n,
                          if D.δ0 ≤ (D.sumruleData.summand i).δ then
                            xi_offcritical_count_bound_by_integrated_defect_singleMass D.ρ D.δ0
                          else 0 := by
                            rw [xi_offcritical_count_bound_by_integrated_defect_activeSet,
                              Finset.sum_filter]
      _ ≤ ∑ i, (D.sumruleData.summand i).defectIntegral := by
            exact Finset.sum_le_sum fun i hi => hterm i
  have hmain :
      (xi_offcritical_count_bound_by_integrated_defect_count D : ℝ) *
          xi_offcritical_count_bound_by_integrated_defect_singleMass D.ρ D.δ0 ≤
        xi_offcritical_count_bound_by_integrated_defect_integratedDefect D := by
    simpa [hintegrated] using hcount_mass
  unfold xi_offcritical_count_bound_by_integrated_defect_data.bound
  exact (le_div_iff₀ D.hSingleMassPos).2 <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain

end

end Omega.Zeta
