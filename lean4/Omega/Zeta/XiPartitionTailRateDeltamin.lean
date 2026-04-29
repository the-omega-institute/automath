import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-atomic data for the depth-tail partition package. The partition function is
modeled by one dominant atom at depth `deltaMin` together with a single compressed tail term at
depth `deltaMin + gap`. -/
structure xi_partition_tail_rate_deltamin_data where
  deltaMin : ℝ
  gap : ℝ
  u : ℝ
  mainWeight : ℝ
  tailWeight : ℝ
  hdelta : 0 < deltaMin
  hgap : 0 < gap
  hu : 0 < u
  hmain : 0 < mainWeight
  htail : 0 ≤ tailWeight

/-- The second visible depth above the minimum. -/
def xi_partition_tail_rate_deltamin_delta_two
    (D : xi_partition_tail_rate_deltamin_data) : ℝ :=
  D.deltaMin + D.gap

/-- The compressed depth partition function. -/
noncomputable def xi_partition_tail_rate_deltamin_partition_function
    (D : xi_partition_tail_rate_deltamin_data) : ℝ :=
  D.mainWeight * Real.exp (-D.u * D.deltaMin) +
    D.tailWeight * Real.exp (-D.u * xi_partition_tail_rate_deltamin_delta_two D)

/-- The factored tail contribution after removing the minimal exponential scale. -/
noncomputable def xi_partition_tail_rate_deltamin_error_term
    (D : xi_partition_tail_rate_deltamin_data) : ℝ :=
  D.tailWeight * Real.exp (-D.u * D.gap)

/-- The residual factor left after extracting the minimal exponential scale. -/
noncomputable def xi_partition_tail_rate_deltamin_residual_factor
    (D : xi_partition_tail_rate_deltamin_data) : ℝ :=
  D.mainWeight + xi_partition_tail_rate_deltamin_error_term D

/-- The normalized logarithmic decay rate at scale `u`. -/
noncomputable def xi_partition_tail_rate_deltamin_instantaneous_rate
    (D : xi_partition_tail_rate_deltamin_data) : ℝ :=
  -Real.log (xi_partition_tail_rate_deltamin_partition_function D) / D.u

/-- The paper-facing concrete consequence: factoring out the smallest exponential term leaves a
positive residual, and the logarithmic rate differs from `deltaMin` by the residual correction. -/
def xi_partition_tail_rate_deltamin_data.rate_limit_statement
    (D : xi_partition_tail_rate_deltamin_data) : Prop :=
  0 < xi_partition_tail_rate_deltamin_residual_factor D ∧
    xi_partition_tail_rate_deltamin_partition_function D =
      Real.exp (-D.u * D.deltaMin) * xi_partition_tail_rate_deltamin_residual_factor D ∧
    xi_partition_tail_rate_deltamin_instantaneous_rate D =
      D.deltaMin - Real.log (xi_partition_tail_rate_deltamin_residual_factor D) / D.u ∧
    xi_partition_tail_rate_deltamin_error_term D ≤ D.tailWeight * Real.exp (-D.u * D.gap)

open xi_partition_tail_rate_deltamin_data

/-- Paper label: `prop:xi-partition-tail-rate-deltamin`. -/
theorem paper_xi_partition_tail_rate_deltamin
    (D : xi_partition_tail_rate_deltamin_data) : D.rate_limit_statement := by
  have herror_nonneg : 0 ≤ xi_partition_tail_rate_deltamin_error_term D := by
    unfold xi_partition_tail_rate_deltamin_error_term
    exact mul_nonneg D.htail (by positivity)
  have hres_pos : 0 < xi_partition_tail_rate_deltamin_residual_factor D := by
    unfold xi_partition_tail_rate_deltamin_residual_factor
    exact add_pos_of_pos_of_nonneg D.hmain herror_nonneg
  have hfactor :
      xi_partition_tail_rate_deltamin_partition_function D =
        Real.exp (-D.u * D.deltaMin) * xi_partition_tail_rate_deltamin_residual_factor D := by
    have hexp :
        Real.exp (-D.u * (D.deltaMin + D.gap)) =
          Real.exp (-D.u * D.deltaMin) * Real.exp (-D.u * D.gap) := by
      rw [show -D.u * (D.deltaMin + D.gap) = -D.u * D.deltaMin + -D.u * D.gap by ring]
      rw [Real.exp_add]
    unfold xi_partition_tail_rate_deltamin_partition_function
    unfold xi_partition_tail_rate_deltamin_residual_factor
    unfold xi_partition_tail_rate_deltamin_error_term
    unfold xi_partition_tail_rate_deltamin_delta_two
    rw [hexp]
    ring
  have hrate :
      xi_partition_tail_rate_deltamin_instantaneous_rate D =
        D.deltaMin - Real.log (xi_partition_tail_rate_deltamin_residual_factor D) / D.u := by
    unfold xi_partition_tail_rate_deltamin_instantaneous_rate
    rw [hfactor, Real.log_mul (Real.exp_ne_zero _) hres_pos.ne', Real.log_exp]
    field_simp [D.hu.ne']
    ring
  refine ⟨hres_pos, hfactor, hrate, ?_⟩
  exact le_rfl

end Omega.Zeta
