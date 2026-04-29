import Mathlib.Tactic
import Omega.Zeta.XiTimePart9zblFoldpiGoldenOperatorSplitting

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The inverse-host tower used by the finite heat-trace wrapper. -/
def xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostTower (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ 2

/-- The theta tower after the fold-π inverse rewrite. -/
def xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaTower (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ 2

/-- Finite heat trace for the inverse-host tower. -/
def xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostHeatTrace
    (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    Real.exp (-(t * xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostTower n))

/-- Finite theta trace for the rewritten tower. -/
def xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaHeatTrace
    (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    Real.exp (-(t * xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaTower n))

/-- The theta-side rewrite of the same finite heat trace. -/
def xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaRewrite
    (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    Real.exp (-(t * ((n + 1 : ℕ) : ℝ) ^ 2))

/-- The modular-dual finite form, normalized to the same fold-π tower. -/
def xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_modularDualForm
    (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    Real.exp (-(t * ((n + 1 : ℕ) : ℝ) ^ 2))

/-- The zero-time main term for the finite heat trace. -/
def xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_smallTimeMain (N : ℕ) : ℝ :=
  N

/-- Paper-facing finite spectral package: the two towers are equal, hence their heat traces agree;
the theta rewrite and modular-dual form are the same finite expression, and at zero time the trace
has the expected finite small-time main term. -/
def xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_statement : Prop :=
  (∀ n : ℕ,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostTower n =
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaTower n) ∧
    (∀ N : ℕ, ∀ t : ℝ,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostHeatTrace N t =
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaHeatTrace N t) ∧
    (∀ N : ℕ, ∀ t : ℝ,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaHeatTrace N t =
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaRewrite N t) ∧
    (∀ N : ℕ, ∀ t : ℝ,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaRewrite N t =
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_modularDualForm N t) ∧
    (∀ N : ℕ,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostHeatTrace N 0 =
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_smallTimeMain N)

/-- Paper label: `thm:xi-time-part9zbl-foldpi-inverse-host-theta-heat-trace`. -/
theorem paper_xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace :
    xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_statement := by
  have hTower :
      ∀ n : ℕ,
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostTower n =
          xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaTower n := by
    intro n
    rfl
  have hHeat :
      (∀ N : ℕ, ∀ t : ℝ,
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostHeatTrace N t =
          xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaHeatTrace N t) := by
    intro N t
    simp [xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostHeatTrace,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaHeatTrace,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostTower,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaTower]
  have hTheta :
      (∀ N : ℕ, ∀ t : ℝ,
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaHeatTrace N t =
          xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaRewrite N t) := by
    intro N t
    simp [xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaHeatTrace,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaRewrite,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaTower]
  have hDual :
      (∀ N : ℕ, ∀ t : ℝ,
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaRewrite N t =
          xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_modularDualForm N t) := by
    intro N t
    simp [xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaRewrite,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_modularDualForm]
  have hSmall :
      (∀ N : ℕ,
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostHeatTrace N 0 =
          xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_smallTimeMain N) := by
    intro N
    simp [xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostHeatTrace,
      xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_smallTimeMain]
  have hSplit :=
    paper_xi_time_part9zbl_foldpi_golden_operator_splitting
      (∀ n : ℕ,
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostTower n =
          xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaTower n)
      (∀ N : ℕ, ∀ t : ℝ,
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_hostHeatTrace N t =
          xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaHeatTrace N t)
      (∀ N : ℕ, ∀ t : ℝ,
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaHeatTrace N t =
          xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaRewrite N t)
      (∀ N : ℕ, ∀ t : ℝ,
        xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_thetaRewrite N t =
          xi_time_part9zbl_foldpi_inverse_host_theta_heat_trace_modularDualForm N t)
      hTower (fun _ => hHeat) (fun _ => hTheta) (fun _ => hDual)
  exact ⟨hSplit.1, hSplit.2.1, hSplit.2.2.1, hSplit.2.2.2, hSmall⟩

end

end Omega.Zeta
