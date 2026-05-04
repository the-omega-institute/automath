import Omega.Conclusion.FrozenEscortTvRigidity

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite data for the frozen escort/microcanonical collapse. The microcanonical law is
the same uniform law on the maximal fiber and vanishes off it, so the escort-to-microcanonical
distance is controlled by the existing frozen-tail bound. -/
structure xi_time_part75a_frozen_escort_microcanonical_collapse_Data where
  tvData : Omega.Conclusion.FrozenEscortTvRigidityData
  microcanonicalLaw : tvData.α → ℝ
  microcanonicalDistance : ℝ
  microcanonicalDistance_def :
    microcanonicalDistance =
      Omega.Conclusion.frozenEscortL1Distance tvData.escortLaw microcanonicalLaw
  microcanonical_eq_uniform_on_max :
    ∀ x, x ∈ tvData.maxFiber → microcanonicalLaw x = tvData.uniformLaw x
  microcanonical_off_max : ∀ x, x ∉ tvData.maxFiber → microcanonicalLaw x = 0

namespace xi_time_part75a_frozen_escort_microcanonical_collapse_Data

/-- The concrete collapse claim: the escort law is exponentially close in finite `L¹` distance to
the microcanonical law on the maximal fiber. -/
def microcanonicalCollapse
    (D : xi_time_part75a_frozen_escort_microcanonical_collapse_Data) : Prop :=
  D.microcanonicalDistance ≤ Real.exp (-D.tvData.exponentialGap)

end xi_time_part75a_frozen_escort_microcanonical_collapse_Data

/-- Paper label: `thm:xi-time-part75a-frozen-escort-microcanonical-collapse`. -/
theorem paper_xi_time_part75a_frozen_escort_microcanonical_collapse
    (D : xi_time_part75a_frozen_escort_microcanonical_collapse_Data) :
    D.microcanonicalCollapse := by
  have hmicro_eq_uniform : ∀ x, D.microcanonicalLaw x = D.tvData.uniformLaw x := by
    intro x
    by_cases hx : x ∈ D.tvData.maxFiber
    · exact D.microcanonical_eq_uniform_on_max x hx
    · rw [D.microcanonical_off_max x hx, D.tvData.uniform_off_max x hx]
  have hdistance :
      D.microcanonicalDistance = D.tvData.tvDistance := by
    rw [D.microcanonicalDistance_def, D.tvData.tvDistance_def]
    unfold Omega.Conclusion.frozenEscortL1Distance
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [hmicro_eq_uniform x]
  have htv := Omega.Conclusion.paper_conclusion_frozen_escort_tv_rigidity D.tvData
  unfold xi_time_part75a_frozen_escort_microcanonical_collapse_Data.microcanonicalCollapse
  rw [hdistance]
  exact htv.2

end Omega.Zeta
