import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-one-order-saturation-forces-all-escort-collapse`. -/
theorem paper_conclusion_one_order_saturation_forces_all_escort_collapse
    (oneOrderSaturation frozenPhase allEscortCollapse : Prop)
    (hfreeze : oneOrderSaturation → frozenPhase)
    (hattractor : frozenPhase → allEscortCollapse) :
    oneOrderSaturation → allEscortCollapse := by
  intro hsaturation
  exact hattractor (hfreeze hsaturation)

end Omega.Conclusion
