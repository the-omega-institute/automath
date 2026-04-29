import Mathlib.Tactic

namespace Omega.Zeta.XiTimePart9jSoftFirstfitConjectureInstance

/-- Paper label: `cor:xi-time-part9j-soft-firstfit-conjecture-instance`. -/
theorem paper_xi_time_part9j_soft_firstfit_conjecture_instance
    (fixedTempImpossible noZeroError noAETerminatingZeroFailure : Prop)
    (hNoZero : fixedTempImpossible → noZeroError)
    (hNoAE : fixedTempImpossible → noAETerminatingZeroFailure)
    (hFixed : fixedTempImpossible) : noZeroError ∧ noAETerminatingZeroFailure := by
  exact ⟨hNoZero hFixed, hNoAE hFixed⟩

end Omega.Zeta.XiTimePart9jSoftFirstfitConjectureInstance
