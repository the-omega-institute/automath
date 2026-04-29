import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete asymptotic-probe data for the endpoint logarithmic window depth lower bound. -/
structure xi_endpoint_logwindow_depth_lower_bound_data where
  A0 : ℝ
  epsilon : ℝ
  N : ℝ
  logN : ℝ

/-- The rearranged leading probe estimate used by the endpoint-window lower bound. -/
def xi_endpoint_logwindow_depth_lower_bound_data.asymptoticProbe
    (D : xi_endpoint_logwindow_depth_lower_bound_data) : Prop :=
  0 < D.epsilon ∧
    (Real.pi * D.A0 ^ 2 / 4) * D.logN ^ 2 ≤ D.epsilon ^ 2 * D.N

/-- The resulting depth lower bound, including the horizon-measure specialization. -/
def xi_endpoint_logwindow_depth_lower_bound_data.depthLowerBound
    (D : xi_endpoint_logwindow_depth_lower_bound_data) : Prop :=
  D.N ≥ (Real.pi * D.A0 ^ 2 / (4 * D.epsilon ^ 2)) * D.logN ^ 2 ∧
    (D.A0 = 1 / (2 * Real.pi) →
      D.N ≥ (1 / (16 * Real.pi * D.epsilon ^ 2)) * D.logN ^ 2)

/-- Paper label: `prop:xi-endpoint-logwindow-depth-lower-bound`. -/
theorem paper_xi_endpoint_logwindow_depth_lower_bound
    (D : xi_endpoint_logwindow_depth_lower_bound_data) :
    D.asymptoticProbe → D.depthLowerBound := by
  intro hProbe
  rcases hProbe with ⟨heps, hlead⟩
  have heps2 : 0 < D.epsilon ^ 2 := sq_pos_of_ne_zero (ne_of_gt heps)
  have hmain :
      D.N ≥ (Real.pi * D.A0 ^ 2 / (4 * D.epsilon ^ 2)) * D.logN ^ 2 := by
    rw [ge_iff_le]
    calc
      (Real.pi * D.A0 ^ 2 / (4 * D.epsilon ^ 2)) * D.logN ^ 2
          = ((Real.pi * D.A0 ^ 2 / 4) * D.logN ^ 2) / D.epsilon ^ 2 := by
            field_simp [ne_of_gt heps2]
      _ ≤ (D.epsilon ^ 2 * D.N) / D.epsilon ^ 2 :=
            div_le_div_of_nonneg_right hlead (le_of_lt heps2)
      _ = D.N := by
            field_simp [ne_of_gt heps2]
  refine ⟨hmain, ?_⟩
  intro hA0
  rw [ge_iff_le] at hmain ⊢
  calc
    (1 / (16 * Real.pi * D.epsilon ^ 2)) * D.logN ^ 2
        = (Real.pi * D.A0 ^ 2 / (4 * D.epsilon ^ 2)) * D.logN ^ 2 := by
          rw [hA0]
          have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
          field_simp [hpi]
          ring
    _ ≤ D.N := hmain

end Omega.Zeta
