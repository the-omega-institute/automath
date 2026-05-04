namespace Omega.Zeta

/-- Paper label: `thm:xi-s4-boundary-vanishing-cycle-induced-module`. -/
theorem paper_xi_s4_boundary_vanishing_cycle_induced_module
    (collisionPair subgroupGenerated inducedRepresentation centralFiberDescription
      torusRankIndex : Prop)
    (hSubgroup : collisionPair → subgroupGenerated)
    (hInduced : subgroupGenerated → inducedRepresentation)
    (hFiber : inducedRepresentation → centralFiberDescription)
    (hRank : centralFiberDescription → torusRankIndex) :
    collisionPair →
      subgroupGenerated ∧ inducedRepresentation ∧ centralFiberDescription ∧ torusRankIndex := by
  intro hCollision
  have hGenerated : subgroupGenerated := hSubgroup hCollision
  have hRepresentation : inducedRepresentation := hInduced hGenerated
  have hFiberDescription : centralFiberDescription := hFiber hRepresentation
  exact ⟨hGenerated, hRepresentation, hFiberDescription, hRank hFiberDescription⟩

end Omega.Zeta
