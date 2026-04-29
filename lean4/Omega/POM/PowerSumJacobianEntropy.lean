import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete Jacobian data for the power-sum coordinate chart. The collision product packages the
absolute Vandermonde factor from the preceding Jacobian formula. -/
structure PomPowerSumJacobianEntropyData where
  n : ℕ
  vandermondeJacobian : ℝ
  collisionProduct : ℝ
  collisionProduct_pos : 0 < collisionProduct
  jacobian_abs :
    |vandermondeJacobian| = (Nat.factorial n : ℝ) * collisionProduct

/-- The coordinate entropy `-log |det DΦ|`. -/
noncomputable def PomPowerSumJacobianEntropyData.coordEntropy
    (D : PomPowerSumJacobianEntropyData) : ℝ :=
  -Real.log |D.vandermondeJacobian|

/-- The factorial contribution `-log n!`. -/
noncomputable def PomPowerSumJacobianEntropyData.factorialLogTerm
    (D : PomPowerSumJacobianEntropyData) : ℝ :=
  -Real.log (Nat.factorial D.n)

/-- The packaged finite collision log-sum, written as the logarithm of the collision product. -/
noncomputable def PomPowerSumJacobianEntropyData.collisionLogSum
    (D : PomPowerSumJacobianEntropyData) : ℝ :=
  Real.log D.collisionProduct

/-- `cor:pom-power-sum-jacobian-entropy` -/
theorem paper_pom_power_sum_jacobian_entropy (D : PomPowerSumJacobianEntropyData) :
    D.coordEntropy = D.factorialLogTerm - D.collisionLogSum := by
  have hfac : 0 < (Nat.factorial D.n : ℝ) := by
    exact_mod_cast Nat.factorial_pos D.n
  rw [PomPowerSumJacobianEntropyData.coordEntropy, PomPowerSumJacobianEntropyData.factorialLogTerm,
    PomPowerSumJacobianEntropyData.collisionLogSum, D.jacobian_abs, Real.log_mul hfac.ne'
      D.collisionProduct_pos.ne']
  ring

end Omega.POM
