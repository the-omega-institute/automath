import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete Jacobian data for the power-sum map. The Vandermonde product is the collision factor
appearing after differentiating the power sums, while positivity records the nondegeneracy needed
for the tangent-map rank statement. -/
structure PomPowerSumVandermondeJacobianData where
  n : ℕ
  vandermondeProduct : ℝ
  vandermondeProduct_pos : 0 < vandermondeProduct

/-- The full Jacobian determinant factors as `n!` times the Vandermonde product. -/
noncomputable def PomPowerSumVandermondeJacobianData.jacobianDet
    (D : PomPowerSumVandermondeJacobianData) : ℝ :=
  (Nat.factorial D.n : ℝ) * D.vandermondeProduct

/-- On the simplex tangent hyperplane, nonzero Jacobian determinant is the packaged full-rank
criterion used by the paper statement. -/
def PomPowerSumVandermondeJacobianData.tangentMapFullRank
    (D : PomPowerSumVandermondeJacobianData) : Prop :=
  0 < D.jacobianDet

/-- Paper label: `thm:pom-power-sum-vandermonde-jacobian`. -/
theorem paper_pom_power_sum_vandermonde_jacobian (D : PomPowerSumVandermondeJacobianData) :
    D.jacobianDet = (Nat.factorial D.n : ℝ) * D.vandermondeProduct ∧ D.tangentMapFullRank := by
  refine ⟨rfl, ?_⟩
  have hfac : 0 < (Nat.factorial D.n : ℝ) := by
    exact_mod_cast Nat.factorial_pos D.n
  simpa [PomPowerSumVandermondeJacobianData.jacobianDet,
    PomPowerSumVandermondeJacobianData.tangentMapFullRank] using
    mul_pos hfac D.vandermondeProduct_pos

/-- Paper label: `cor:pom-power-sum-local-chart`. -/
theorem paper_pom_power_sum_local_chart (D : PomPowerSumVandermondeJacobianData) :
    D.tangentMapFullRank := by
  exact (paper_pom_power_sum_vandermonde_jacobian D).2

end Omega.POM
