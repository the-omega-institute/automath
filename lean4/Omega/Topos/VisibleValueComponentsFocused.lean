import Omega.Topos.VisibleValueComponents

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Focused-publication wrapper for visible value classes as global connected components in
    `2026_conservative_extension_chain_state_forcing_apal_focused`.
    thm:visible-value-components -/
theorem paper_conservative_extension_visible_value_components_focused
    {VisibleValueClass SheafSection ConnectedComponent : Type}
    (visibleToSheaf : Equiv VisibleValueClass SheafSection)
    (sheafToConnected : Equiv SheafSection ConnectedComponent) :
    Nonempty
      ((Equiv VisibleValueClass SheafSection) ×
        (Equiv SheafSection ConnectedComponent) ×
        (Equiv VisibleValueClass ConnectedComponent)) :=
  paper_gluing_failure_visible_value_components visibleToSheaf sheafToConnected

end Omega.Topos
