import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.ProfiniteAxisChebotarev

namespace Omega.POM

noncomputable section

/-- Concrete data for the profinite-cylinder capacity inequality. The multiplicative hypothesis is
the packaged relative-error estimate obtained from the profinite-axis Chebotarev wrapper under the
uniform spectral-gap regime. -/
structure POMProfiniteCylinderCapacityData where
  groupCard : ℕ
  lambdaValue : ℝ
  epsilon : ℝ
  delta : ℝ
  n : ℝ
  hcard : 1 ≤ groupCard
  hlambda : 0 < lambdaValue
  hdelta : 0 < delta
  relativeErrorBound :
    (groupCard : ℝ) ≤ delta * lambdaValue ^ (((1 / 2 : ℝ) + epsilon) * n)

namespace POMProfiniteCylinderCapacityData

/-- The logarithmic size of the finite quotient group. -/
def logGroupCard (D : POMProfiniteCylinderCapacityData) : ℝ :=
  Real.log (D.groupCard : ℝ)

/-- The available capacity budget coming from the time-length and relative-error parameters. -/
def capacityBudget (D : POMProfiniteCylinderCapacityData) : ℝ :=
  (((1 / 2 : ℝ) + D.epsilon) * D.n) * Real.log D.lambdaValue - Real.log (1 / D.delta)

end POMProfiniteCylinderCapacityData

open POMProfiniteCylinderCapacityData

/-- Paper label: `cor:pom-profinite-cylinder-capacity`. -/
theorem paper_pom_profinite_cylinder_capacity (D : POMProfiniteCylinderCapacityData) :
    D.logGroupCard <= D.capacityBudget := by
  have hcard_pos : 0 < (D.groupCard : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one D.hcard
  have hpow_pos :
      0 < D.lambdaValue ^ (((1 / 2 : ℝ) + D.epsilon) * D.n) := by
    exact Real.rpow_pos_of_pos D.hlambda _
  have hlog :
      Real.log (D.groupCard : ℝ) ≤
        Real.log (D.delta * D.lambdaValue ^ (((1 / 2 : ℝ) + D.epsilon) * D.n)) := by
    exact Real.log_le_log hcard_pos D.relativeErrorBound
  calc
    D.logGroupCard = Real.log (D.groupCard : ℝ) := rfl
    _ ≤ Real.log (D.delta * D.lambdaValue ^ (((1 / 2 : ℝ) + D.epsilon) * D.n)) := hlog
    _ = Real.log D.delta + ((((1 / 2 : ℝ) + D.epsilon) * D.n) * Real.log D.lambdaValue) := by
          rw [Real.log_mul (ne_of_gt D.hdelta) hpow_pos.ne', Real.log_rpow D.hlambda]
    _ = (((1 / 2 : ℝ) + D.epsilon) * D.n) * Real.log D.lambdaValue - Real.log (1 / D.delta) := by
          have hloginv : Real.log (1 / D.delta) = -Real.log D.delta := by
            rw [one_div]
            exact Real.log_inv D.delta
          have hloginv' : -Real.log (1 / D.delta) = Real.log D.delta := by
            rw [hloginv]
            ring
          linarith
    _ = D.capacityBudget := by
          rfl

end

end Omega.POM
