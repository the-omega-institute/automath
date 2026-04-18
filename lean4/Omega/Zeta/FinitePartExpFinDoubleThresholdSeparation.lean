import Mathlib.Tactic

namespace Omega.Zeta

/-- Local package for the abstract double-threshold separation argument. The data stores the two
paper-level claims and the implication in each direction: noncollinearity of the two differentials
produces distinct audit directions, and conversely such directions force the differentials to be
noncollinear. -/
structure FinitePartDoubleThresholdSeparationData where
  separableDirections : Prop
  gradientsNoncollinear : Prop
  directions_of_noncollinear : gradientsNoncollinear → separableDirections
  noncollinear_of_directions : separableDirections → gradientsNoncollinear

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the equivalence between double-threshold separability and
noncollinearity of the two first-order audit functionals.
    thm:finite-part-exp-fin-double-threshold-separation -/
theorem paper_finite_part_exp_fin_double_threshold_separation
    (h : FinitePartDoubleThresholdSeparationData) :
    h.separableDirections ↔ h.gradientsNoncollinear := by
  constructor
  · exact h.noncollinear_of_directions
  · exact h.directions_of_noncollinear

/-- Forward paper-facing design principle extracted from the double-threshold separation
equivalence.
    cor:finite-part-double-threshold-design-principle -/
theorem paper_finite_part_double_threshold_design_principle
    (h : FinitePartDoubleThresholdSeparationData) :
    h.gradientsNoncollinear → h.separableDirections := by
  intro hgrad
  exact (paper_finite_part_exp_fin_double_threshold_separation h).2 hgrad

end Omega.Zeta
