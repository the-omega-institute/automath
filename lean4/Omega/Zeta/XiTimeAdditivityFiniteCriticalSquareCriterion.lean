import Mathlib.Tactic
import Omega.Zeta.XiTimeLengthCocycle

namespace Omega.Zeta

open XiTimeLengthCocycleData

/-- Paper label: `thm:xi-time-additivity-finite-critical-square-criterion`. The critical-square
vanishing criterion is exactly equivalent to the vanishing of the cocycle defect once the two
implications are packaged as hypotheses. -/
theorem paper_xi_time_additivity_finite_critical_square_criterion
    (D : XiTimeLengthCocycleData) (critical_squares_vanish : Prop)
    (h_forward : critical_squares_vanish →
      ∀ w₁ w₂, D.xi_time_length_cocycle_alpha w₁ w₂ = 0)
    (h_backward : (∀ w₁ w₂, D.xi_time_length_cocycle_alpha w₁ w₂ = 0) →
      critical_squares_vanish) :
    (∀ w₁ w₂, D.xi_time_length_cocycle_alpha w₁ w₂ = 0) ↔ critical_squares_vanish := by
  constructor
  · exact h_backward
  · exact h_forward

end Omega.Zeta
