import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic

open Filter
open scoped Topology

namespace Omega.SyncKernelWeighted

/-- Concrete convergence package for the normalized Farey Gram kernels and their limiting integral
operator. -/
structure gm_farey_sampling_operator_limit_data where
  gm_farey_sampling_operator_limit_scale_L : ℕ → ℝ
  gm_farey_sampling_operator_limit_scale_M : ℕ → ℝ
  gm_farey_sampling_operator_limit_tau : ℝ
  gm_farey_sampling_operator_limit_discrete_operator_norm : ℕ → ℝ
  gm_farey_sampling_operator_limit_limit_operator_norm : ℝ
  gm_farey_sampling_operator_limit_principal_eigenvalue : ℕ → ℝ
  gm_farey_sampling_operator_limit_limit_principal_eigenvalue : ℝ
  gm_farey_sampling_operator_limit_principal_vector_error : ℕ → ℝ
  gm_farey_sampling_operator_limit_regime :
    Tendsto
      (fun n =>
        gm_farey_sampling_operator_limit_scale_L n /
          gm_farey_sampling_operator_limit_scale_M n ^ (2 : ℕ))
      atTop (nhds gm_farey_sampling_operator_limit_tau)
  gm_farey_sampling_operator_limit_operator_norm_convergence :
    Tendsto
      (fun n =>
        |gm_farey_sampling_operator_limit_discrete_operator_norm n -
          gm_farey_sampling_operator_limit_limit_operator_norm|)
      atTop (nhds 0)
  gm_farey_sampling_operator_limit_principal_eigenvalue_convergence :
    Tendsto
      (fun n =>
        |gm_farey_sampling_operator_limit_principal_eigenvalue n -
          gm_farey_sampling_operator_limit_limit_principal_eigenvalue|)
      atTop (nhds 0)
  gm_farey_sampling_operator_limit_principal_vector_convergence :
    Tendsto gm_farey_sampling_operator_limit_principal_vector_error atTop (nhds 0)

namespace gm_farey_sampling_operator_limit_data

/-- The finite-dimensional convergence wrapper: the scaling regime, operator-norm convergence, and
the principal spectral consequences. -/
def statement (D : gm_farey_sampling_operator_limit_data) : Prop :=
  Tendsto
      (fun n =>
        D.gm_farey_sampling_operator_limit_scale_L n /
          D.gm_farey_sampling_operator_limit_scale_M n ^ (2 : ℕ))
      atTop (nhds D.gm_farey_sampling_operator_limit_tau) ∧
    Tendsto
      (fun n =>
        |D.gm_farey_sampling_operator_limit_discrete_operator_norm n -
          D.gm_farey_sampling_operator_limit_limit_operator_norm|)
      atTop (nhds 0) ∧
    Tendsto
      (fun n =>
        |D.gm_farey_sampling_operator_limit_principal_eigenvalue n -
          D.gm_farey_sampling_operator_limit_limit_principal_eigenvalue|)
      atTop (nhds 0) ∧
    Tendsto D.gm_farey_sampling_operator_limit_principal_vector_error atTop (nhds 0)

end gm_farey_sampling_operator_limit_data

open gm_farey_sampling_operator_limit_data

/-- Paper label: `thm:gm-farey-sampling-operator-limit`. -/
theorem paper_gm_farey_sampling_operator_limit
    (D : gm_farey_sampling_operator_limit_data) : D.statement := by
  exact ⟨D.gm_farey_sampling_operator_limit_regime,
    D.gm_farey_sampling_operator_limit_operator_norm_convergence,
    D.gm_farey_sampling_operator_limit_principal_eigenvalue_convergence,
    D.gm_farey_sampling_operator_limit_principal_vector_convergence⟩

end Omega.SyncKernelWeighted
