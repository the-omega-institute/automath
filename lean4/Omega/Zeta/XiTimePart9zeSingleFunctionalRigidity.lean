import Omega.Zeta.XiTimePart9xaaSingleFunctionalRigidity

namespace Omega.Zeta

/-- The `9ze` single-functional rigidity statement reuses the concrete Wulff-Schur data package
from the universal convex-envelope theorem. -/
def xi_time_part9ze_single_functional_rigidity_statement : Prop :=
  ∀ D : xi_time_part9xaa_single_functional_rigidity_Data,
    (D.collisionMinimal → D.wulffRay)
      ∧ (D.gaugeVolumeMinimal → D.wulffRay)
      ∧ (D.entropyGapMinimal → D.wulffRay)

/-- Paper label: `thm:xi-time-part9ze-single-functional-rigidity`. -/
theorem paper_xi_time_part9ze_single_functional_rigidity :
    xi_time_part9ze_single_functional_rigidity_statement := by
  intro D
  exact
    ⟨xi_time_part9xaa_single_functional_rigidity_collision_rigidity D,
      xi_time_part9xaa_single_functional_rigidity_gauge_volume_rigidity D,
      xi_time_part9xaa_single_functional_rigidity_entropy_gap_rigidity D⟩

end Omega.Zeta
