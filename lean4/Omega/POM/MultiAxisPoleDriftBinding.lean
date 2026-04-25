import Mathlib.Tactic
import Omega.POM.MultiAxisNear1PoleBarrier
import Omega.SyncKernelWeighted.RealInput40SpaceTimeConversionLaw

namespace Omega.POM

/-- Concrete data for binding the unavoidable near-`1` pole gap to the finite-part drift carried
by the same short direction.  The factor coming from the conversion law is bounded uniformly on
the relevant unit-sphere slice. -/
structure pom_multi_axis_pole_drift_binding_data where
  pom_multi_axis_pole_drift_binding_d : ℕ
  pom_multi_axis_pole_drift_binding_sigmaDiag :
    Fin pom_multi_axis_pole_drift_binding_d → ℝ
  pom_multi_axis_pole_drift_binding_Λ :
    Finset (Fin pom_multi_axis_pole_drift_binding_d → ℝ)
  pom_multi_axis_pole_drift_binding_hΛ :
    pom_multi_axis_pole_drift_binding_Λ.Nonempty
  pom_multi_axis_pole_drift_binding_Vd : ℝ
  pom_multi_axis_pole_drift_binding_detSigma : ℝ
  pom_multi_axis_pole_drift_binding_B : ℝ
  pom_multi_axis_pole_drift_binding_r : ℝ
  pom_multi_axis_pole_drift_binding_deltaSpec : ℝ
  pom_multi_axis_pole_drift_binding_poleGap : ℝ
  pom_multi_axis_pole_drift_binding_theta :
    Fin pom_multi_axis_pole_drift_binding_d → ℝ
  pom_multi_axis_pole_drift_binding_htheta_mem :
    pom_multi_axis_pole_drift_binding_theta ∈ pom_multi_axis_pole_drift_binding_Λ
  pom_multi_axis_pole_drift_binding_htheta_budget :
    Omega.POM.pomQuadraticEnergy
        pom_multi_axis_pole_drift_binding_sigmaDiag
        pom_multi_axis_pole_drift_binding_theta ≤
      pom_multi_axis_pole_drift_binding_r ^ 2
  pom_multi_axis_pole_drift_binding_hr :
    pom_multi_axis_pole_drift_binding_r ^ 2 =
      Omega.POM.pomMinkowskiBudgetUpperBound
        pom_multi_axis_pole_drift_binding_d
        pom_multi_axis_pole_drift_binding_Vd
        pom_multi_axis_pole_drift_binding_detSigma
        pom_multi_axis_pole_drift_binding_B
  pom_multi_axis_pole_drift_binding_hgap :
    pom_multi_axis_pole_drift_binding_deltaSpec =
      (1 / 2 : ℝ) *
        Omega.POM.pomShortestEnergy
          pom_multi_axis_pole_drift_binding_sigmaDiag
          pom_multi_axis_pole_drift_binding_Λ
          pom_multi_axis_pole_drift_binding_hΛ
  pom_multi_axis_pole_drift_binding_conversion :
    Omega.SyncKernelWeighted.real_input_40_space_time_conversion_law_data
  pom_multi_axis_pole_drift_binding_t : ℝ
  pom_multi_axis_pole_drift_binding_hpole :
    pom_multi_axis_pole_drift_binding_poleGap =
      pom_multi_axis_pole_drift_binding_deltaSpec /
        pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_logLambda
  pom_multi_axis_pole_drift_binding_hpole_eval :
    pom_multi_axis_pole_drift_binding_poleGap =
      pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_poleGap
        pom_multi_axis_pole_drift_binding_t
  pom_multi_axis_pole_drift_binding_hpole_nonneg :
    0 ≤ pom_multi_axis_pole_drift_binding_poleGap
  pom_multi_axis_pole_drift_binding_drift : ℝ
  pom_multi_axis_pole_drift_binding_hdrift :
    pom_multi_axis_pole_drift_binding_drift =
      pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_finitepartDrift
        pom_multi_axis_pole_drift_binding_t
  pom_multi_axis_pole_drift_binding_conversion_factor_bound : ℝ
  pom_multi_axis_pole_drift_binding_conversion_factor_bound_nonneg :
    0 ≤ pom_multi_axis_pole_drift_binding_conversion_factor_bound
  pom_multi_axis_pole_drift_binding_hconverted :
    |(pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_logLambda *
          pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_directionalCoupling) *
        pom_multi_axis_pole_drift_binding_poleGap +
      pom_multi_axis_pole_drift_binding_t ^ 4 *
        Omega.SyncKernelWeighted.real_input_40_space_time_conversion_law_remainder
          pom_multi_axis_pole_drift_binding_conversion
          pom_multi_axis_pole_drift_binding_t| ≤
      pom_multi_axis_pole_drift_binding_conversion_factor_bound *
        pom_multi_axis_pole_drift_binding_poleGap

/-- The unavoidable short pole direction carries finite-part drift of the same `B^{-2 / d}` order,
with the constant amplified only by the bounded directional conversion factor. -/
def pom_multi_axis_pole_drift_binding_statement
    (D : pom_multi_axis_pole_drift_binding_data) : Prop :=
  |D.pom_multi_axis_pole_drift_binding_drift| ≤
    D.pom_multi_axis_pole_drift_binding_conversion_factor_bound *
      (Omega.POM.pomMinkowskiBudgetUpperBound
          D.pom_multi_axis_pole_drift_binding_d
          D.pom_multi_axis_pole_drift_binding_Vd
          D.pom_multi_axis_pole_drift_binding_detSigma
          D.pom_multi_axis_pole_drift_binding_B /
        (2 * D.pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_logLambda))

/-- Paper label: `cor:pom-multi-axis-pole-drift-binding`. -/
theorem paper_pom_multi_axis_pole_drift_binding
    (D : pom_multi_axis_pole_drift_binding_data) :
    pom_multi_axis_pole_drift_binding_statement D := by
  have hconv :=
    Omega.SyncKernelWeighted.paper_real_input_40_space_time_conversion_law
      D.pom_multi_axis_pole_drift_binding_conversion
      D.pom_multi_axis_pole_drift_binding_t
  have hconverted_eq :
      D.pom_multi_axis_pole_drift_binding_drift =
        (D.pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_logLambda *
            D.pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_directionalCoupling) *
          D.pom_multi_axis_pole_drift_binding_poleGap +
        D.pom_multi_axis_pole_drift_binding_t ^ 4 *
          Omega.SyncKernelWeighted.real_input_40_space_time_conversion_law_remainder
            D.pom_multi_axis_pole_drift_binding_conversion
            D.pom_multi_axis_pole_drift_binding_t := by
    rw [D.pom_multi_axis_pole_drift_binding_hdrift, hconv, D.pom_multi_axis_pole_drift_binding_hpole_eval]
  have hpole_bound :
      D.pom_multi_axis_pole_drift_binding_poleGap ≤
        Omega.POM.pomMinkowskiBudgetUpperBound
            D.pom_multi_axis_pole_drift_binding_d
            D.pom_multi_axis_pole_drift_binding_Vd
            D.pom_multi_axis_pole_drift_binding_detSigma
            D.pom_multi_axis_pole_drift_binding_B /
          (2 * D.pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_logLambda) := by
    simpa [D.pom_multi_axis_pole_drift_binding_hpole] using
      (paper_pom_multi_axis_near1_pole_barrier
        D.pom_multi_axis_pole_drift_binding_sigmaDiag
        D.pom_multi_axis_pole_drift_binding_Λ
        D.pom_multi_axis_pole_drift_binding_hΛ
        D.pom_multi_axis_pole_drift_binding_Vd
        D.pom_multi_axis_pole_drift_binding_detSigma
        D.pom_multi_axis_pole_drift_binding_B
        D.pom_multi_axis_pole_drift_binding_r
        D.pom_multi_axis_pole_drift_binding_deltaSpec
        D.pom_multi_axis_pole_drift_binding_poleGap
        D.pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_logLambda
        D.pom_multi_axis_pole_drift_binding_theta
        D.pom_multi_axis_pole_drift_binding_htheta_mem
        D.pom_multi_axis_pole_drift_binding_htheta_budget
        D.pom_multi_axis_pole_drift_binding_hr
        D.pom_multi_axis_pole_drift_binding_hgap
        D.pom_multi_axis_pole_drift_binding_hpole
        D.pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_logLambda_pos)
  have habs_drift :
      |D.pom_multi_axis_pole_drift_binding_drift| ≤
        D.pom_multi_axis_pole_drift_binding_conversion_factor_bound *
          D.pom_multi_axis_pole_drift_binding_poleGap := by
    rw [hconverted_eq]
    exact D.pom_multi_axis_pole_drift_binding_hconverted
  have hmul_bound :
      D.pom_multi_axis_pole_drift_binding_conversion_factor_bound *
          D.pom_multi_axis_pole_drift_binding_poleGap ≤
        D.pom_multi_axis_pole_drift_binding_conversion_factor_bound *
          (Omega.POM.pomMinkowskiBudgetUpperBound
              D.pom_multi_axis_pole_drift_binding_d
              D.pom_multi_axis_pole_drift_binding_Vd
              D.pom_multi_axis_pole_drift_binding_detSigma
              D.pom_multi_axis_pole_drift_binding_B /
            (2 * D.pom_multi_axis_pole_drift_binding_conversion.real_input_40_space_time_conversion_law_logLambda)) := by
    exact mul_le_mul le_rfl hpole_bound
      D.pom_multi_axis_pole_drift_binding_hpole_nonneg
      D.pom_multi_axis_pole_drift_binding_conversion_factor_bound_nonneg
  exact le_trans habs_drift hmul_bound

end Omega.POM
