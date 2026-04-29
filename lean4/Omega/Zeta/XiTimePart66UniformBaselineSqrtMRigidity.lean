import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the relative-uniform baseline rigidity package.  The collision side and
the residual side determine the scaled `L^2` liminf by Parseval; the total-variation scale is
then bounded below by the monotone comparison with the scaled `L^2` quantity. -/
structure xi_time_part66_uniform_baseline_sqrtm_rigidity_data where
  xi_time_part66_uniform_baseline_sqrtm_rigidity_collisionScaledLiminf : ℝ
  xi_time_part66_uniform_baseline_sqrtm_rigidity_residualEnergyLiminf : ℝ
  xi_time_part66_uniform_baseline_sqrtm_rigidity_l2ScaledLiminf : ℝ
  xi_time_part66_uniform_baseline_sqrtm_rigidity_tvScaledLiminf : ℝ
  xi_time_part66_uniform_baseline_sqrtm_rigidity_uniformBaseline : ℝ
  xi_time_part66_uniform_baseline_sqrtm_rigidity_parsevalCollisionIdentity :
    xi_time_part66_uniform_baseline_sqrtm_rigidity_l2ScaledLiminf =
      xi_time_part66_uniform_baseline_sqrtm_rigidity_collisionScaledLiminf -
        xi_time_part66_uniform_baseline_sqrtm_rigidity_residualEnergyLiminf
  xi_time_part66_uniform_baseline_sqrtm_rigidity_residualEnergyLiminfLowerBound :
    xi_time_part66_uniform_baseline_sqrtm_rigidity_uniformBaseline ≤
      xi_time_part66_uniform_baseline_sqrtm_rigidity_collisionScaledLiminf -
        xi_time_part66_uniform_baseline_sqrtm_rigidity_residualEnergyLiminf
  xi_time_part66_uniform_baseline_sqrtm_rigidity_tvL2Comparison :
    xi_time_part66_uniform_baseline_sqrtm_rigidity_l2ScaledLiminf / 2 ≤
      xi_time_part66_uniform_baseline_sqrtm_rigidity_tvScaledLiminf

/-- The scaled `L^2` liminf remains at least the uniform-baseline constant. -/
def xi_time_part66_uniform_baseline_sqrtm_rigidity_data.l2Bound
    (D : xi_time_part66_uniform_baseline_sqrtm_rigidity_data) : Prop :=
  D.xi_time_part66_uniform_baseline_sqrtm_rigidity_uniformBaseline ≤
    D.xi_time_part66_uniform_baseline_sqrtm_rigidity_l2ScaledLiminf

/-- The total-variation scale inherits half of the scaled `L^2` baseline lower bound. -/
def xi_time_part66_uniform_baseline_sqrtm_rigidity_data.tvBound
    (D : xi_time_part66_uniform_baseline_sqrtm_rigidity_data) : Prop :=
  D.xi_time_part66_uniform_baseline_sqrtm_rigidity_uniformBaseline / 2 ≤
    D.xi_time_part66_uniform_baseline_sqrtm_rigidity_tvScaledLiminf

/-- Paper label: `thm:xi-time-part66-uniform-baseline-sqrtM-rigidity`. -/
theorem paper_xi_time_part66_uniform_baseline_sqrtm_rigidity
    (D : xi_time_part66_uniform_baseline_sqrtm_rigidity_data) :
    D.l2Bound ∧ D.tvBound := by
  have hl2 : D.l2Bound := by
    calc
      D.xi_time_part66_uniform_baseline_sqrtm_rigidity_uniformBaseline
          ≤ D.xi_time_part66_uniform_baseline_sqrtm_rigidity_collisionScaledLiminf -
              D.xi_time_part66_uniform_baseline_sqrtm_rigidity_residualEnergyLiminf :=
            D.xi_time_part66_uniform_baseline_sqrtm_rigidity_residualEnergyLiminfLowerBound
      _ = D.xi_time_part66_uniform_baseline_sqrtm_rigidity_l2ScaledLiminf :=
            D.xi_time_part66_uniform_baseline_sqrtm_rigidity_parsevalCollisionIdentity.symm
  have htv : D.tvBound := by
    have hmono :
        D.xi_time_part66_uniform_baseline_sqrtm_rigidity_uniformBaseline / 2 ≤
          D.xi_time_part66_uniform_baseline_sqrtm_rigidity_l2ScaledLiminf / 2 := by
      exact div_le_div_of_nonneg_right hl2 (by norm_num : (0 : ℝ) ≤ 2)
    exact le_trans hmono D.xi_time_part66_uniform_baseline_sqrtm_rigidity_tvL2Comparison
  exact ⟨hl2, htv⟩

end Omega.Zeta
