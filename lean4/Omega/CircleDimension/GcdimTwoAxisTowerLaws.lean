namespace Omega.CircleDimension

/-- Paper-facing package for the two-axis tower laws: the transcendence-degree tower law, the
finite-algebraic preservation of the growth axis together with the lower bound on the algebraic
degree axis, and the common-basis equality case.
    thm:gcdim-two-axis-tower-laws -/
theorem paper_gcdim_two_axis_tower_laws
    (towerAdditivity finiteAlgebraicExtension sameGrowth lowerDegreeBound
      equalityUnderCommonBasis : Prop)
    (hAdd : towerAdditivity)
    (hAlg : finiteAlgebraicExtension -> sameGrowth ∧ lowerDegreeBound)
    (hEq : equalityUnderCommonBasis) :
    towerAdditivity ∧ (finiteAlgebraicExtension -> sameGrowth ∧ lowerDegreeBound) ∧
      equalityUnderCommonBasis := by
  exact ⟨hAdd, hAlg, hEq⟩

end Omega.CircleDimension
