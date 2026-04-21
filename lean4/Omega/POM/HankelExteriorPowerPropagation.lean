import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import Omega.POM.HankelDeterminantGeometricLaw

namespace Omega.POM

/-- Exterior-power propagation for a shifted Hankel family. Once `H (k₀ + r) = H k₀ * A^r`, the
induced maps on `s`-th exterior powers propagate by the same linear dynamics. -/
theorem paper_pom_hankel_exterior_power_propagation
    (D : POMHankelDeterminantGeometricLawData) (s : ℕ) :
    ∀ r,
      exteriorPower.map s (Matrix.toLin' (D.H (D.k0 + r))) =
        exteriorPower.map s (Matrix.toLin' (D.H D.k0)) ∘ₗ
          (exteriorPower.map s (Matrix.toLin' D.A)) ^ r := by
  have hmap_pow :
      ∀ r,
        exteriorPower.map s (Matrix.toLin' (D.A ^ r)) =
          (exteriorPower.map s (Matrix.toLin' D.A)) ^ r := by
    intro r
    induction r with
    | zero =>
        simp [Module.End.one_eq_id]
    | succ r ihr =>
        rw [pow_succ, Matrix.toLin'_mul, exteriorPower.map_comp, ihr, pow_succ,
          Module.End.mul_eq_comp]
  intro r
  rw [D.hshift r, Matrix.toLin'_mul, exteriorPower.map_comp, hmap_pow]

end Omega.POM
