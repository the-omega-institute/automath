import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9f-kolmogorov-fiber-saturation`. -/
theorem paper_xi_time_part9f_kolmogorov_fiber_saturation
    (upperFiberCode tailCountingBound : Prop)
    (hUpper : upperFiberCode)
    (hTail : upperFiberCode -> tailCountingBound) :
    upperFiberCode ∧ tailCountingBound := by
  exact ⟨hUpper, hTail hUpper⟩

end Omega.Zeta
