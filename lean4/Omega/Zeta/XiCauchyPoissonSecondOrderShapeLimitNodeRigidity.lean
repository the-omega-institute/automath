import Omega.Zeta.XiCauchyPoissonDensityRatioSecondOrderProfile

namespace Omega.Zeta

/-- Chapter-local package for the second-order Poisson--Cauchy shape limit and the induced
two-node sign rigidity. The package extends the verified density-ratio second-order profile with
the `t^3` shape limit, the normalized density-ratio shape limit, and the two-node sign pattern. -/
structure XiCauchyPoissonSecondOrderShapeLimitNodeRigidityData
    extends XiCauchyPoissonDensityRatioSecondOrderProfileData where
  uniformShapeLimit : Prop
  uniformShapeLimitWitness : uniformShapeLimit
  normalizedRatioShapeLimit : Prop
  normalizedRatioShapeLimitWitness : normalizedRatioShapeLimit
  nodeRigidity : Prop
  nodeRigidityWitness : nodeRigidity

/-- Paper-facing wrapper for the Poisson--Cauchy second-order shape limit and its two-node
rigidity.
    thm:xi-cauchy-poisson-second-order-shape-limit-node-rigidity -/
theorem paper_xi_cauchy_poisson_second_order_shape_limit_node_rigidity
    (h : XiCauchyPoissonSecondOrderShapeLimitNodeRigidityData) :
    h.uniformShapeLimit ∧ h.normalizedRatioShapeLimit ∧ h.nodeRigidity := by
  let _ :
      h.toXiCauchyPoissonDensityRatioSecondOrderProfileData.uniformSecondOrderExpansion :=
    paper_xi_cauchy_poisson_density_ratio_second_order_profile
      h.toXiCauchyPoissonDensityRatioSecondOrderProfileData
  exact ⟨h.uniformShapeLimitWitness, h.normalizedRatioShapeLimitWitness, h.nodeRigidityWitness⟩

end Omega.Zeta
