import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete endpoint-expansion data for the critical bit density. -/
structure pom_bcrit_small_distortion_expansion_data where
  beta : ℝ
  delta : ℝ
  entropy : ℝ
  halfCollisionConstant : ℝ
  endpointRemainder : ℝ
  rate : ℝ → ℝ
  rate_endpoint_expansion :
    rate delta =
      entropy - delta * Real.log (halfCollisionConstant / delta) + endpointRemainder * delta

/-- Critical bit density, normalized by `log 2`. -/
def pom_bcrit_small_distortion_expansion_bcrit
    (D : pom_bcrit_small_distortion_expansion_data) : ℝ :=
  (1 - D.beta) * D.rate D.delta / Real.log 2

/-- The endpoint expansion of the critical bit density. -/
def pom_bcrit_small_distortion_expansion_law
    (D : pom_bcrit_small_distortion_expansion_data) : Prop :=
  pom_bcrit_small_distortion_expansion_bcrit D =
    (1 - D.beta) / Real.log 2 *
      (D.entropy - D.delta * Real.log (D.halfCollisionConstant / D.delta) +
        D.endpointRemainder * D.delta)

/-- Paper label: `cor:pom-bcrit-small-distortion-expansion`. -/
theorem paper_pom_bcrit_small_distortion_expansion
    (D : pom_bcrit_small_distortion_expansion_data) :
    pom_bcrit_small_distortion_expansion_law D := by
  unfold pom_bcrit_small_distortion_expansion_law
  unfold pom_bcrit_small_distortion_expansion_bcrit
  rw [D.rate_endpoint_expansion]
  ring

end

end Omega.POM
