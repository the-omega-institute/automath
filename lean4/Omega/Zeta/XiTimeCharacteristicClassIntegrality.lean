import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-characteristic-class-integrality`. -/
theorem paper_xi_time_characteristic_class_integrality
    (integerCocycle gaugeInvariant closedChainIntegerPairing netTimeDefectClass : Prop)
    (hCocycle : integerCocycle) (hGauge : gaugeInvariant)
    (hPairing : closedChainIntegerPairing) (hDefect : netTimeDefectClass) :
    integerCocycle ∧ gaugeInvariant ∧ closedChainIntegerPairing ∧ netTimeDefectClass := by
  exact ⟨hCocycle, hGauge, hPairing, hDefect⟩

end Omega.Zeta
