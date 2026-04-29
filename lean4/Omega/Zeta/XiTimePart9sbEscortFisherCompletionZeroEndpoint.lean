import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9sb-escort-fisher-completion-zero-endpoint`. -/
theorem paper_xi_time_part9sb_escort_fisher_completion_zero_endpoint
    (flatCoordinateDistance endpointDistanceFormula diameterFormula onePointCompletion : Prop)
    (hdist : flatCoordinateDistance -> endpointDistanceFormula)
    (hdiam : endpointDistanceFormula -> diameterFormula)
    (hcomp : endpointDistanceFormula -> onePointCompletion)
    (hflat : flatCoordinateDistance) :
    endpointDistanceFormula ∧ diameterFormula ∧ onePointCompletion := by
  have hendpoint : endpointDistanceFormula := hdist hflat
  exact ⟨hendpoint, hdiam hendpoint, hcomp hendpoint⟩

end Omega.Zeta
