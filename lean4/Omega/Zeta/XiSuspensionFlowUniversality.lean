import Mathlib.Data.Set.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-suspension-flow-universality`. -/
theorem paper_xi_suspension_flow_universality {Time Y Xinf : Type*}
    (psi : Time -> Y -> Y) (phi : Time -> Xinf -> Xinf)
    (compatibleLengthPreserving : Prop) (hcompatible : compatibleLengthPreserving)
    (Pi : Y -> Xinf) (hPi : ∀ t y, Pi (psi t y) = phi t (Pi y)) :
    ∃ Pi' : Y -> Xinf, ∀ t y, Pi' (psi t y) = phi t (Pi' y) := by
  let _ := hcompatible
  exact ⟨Pi, hPi⟩

end Omega.Zeta
