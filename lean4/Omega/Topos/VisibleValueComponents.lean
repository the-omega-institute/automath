import Mathlib.Logic.Equiv.Basic

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for visible value classes as sheaf and component data.
    thm:visible-value-components -/
theorem paper_gluing_failure_visible_value_components
    {VisibleValueClass SheafSection ConnectedComponent : Type}
    (visibleToSheaf : Equiv VisibleValueClass SheafSection)
    (sheafToConnected : Equiv SheafSection ConnectedComponent) :
    Nonempty
      ((Equiv VisibleValueClass SheafSection) ×
        (Equiv SheafSection ConnectedComponent) ×
        (Equiv VisibleValueClass ConnectedComponent)) := by
  exact ⟨visibleToSheaf, sheafToConnected, visibleToSheaf.trans sheafToConnected⟩

end Omega.Topos
