import Omega.Topos.ComponentGerbeDecomposition

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Focused-publication wrapper for the visible-branch component-gerbe theorem in
    `2026_conservative_extension_chain_state_forcing_apal_focused`.
    thm:component-gerbe-decomposition -/
theorem paper_conservative_extension_component_gerbe_decomposition_focused
    {Branch : Type}
    (Visible : Branch → Prop)
    (LocallyNonempty : Branch → Prop)
    (LocallyIsomorphic : Branch → Prop)
    (Banded : Branch → Prop)
    (hNonempty : ∀ ⦃v : Branch⦄, Visible v → LocallyNonempty v)
    (hIso : ∀ ⦃v : Branch⦄, Visible v → LocallyIsomorphic v)
    (hBanded : ∀ ⦃v : Branch⦄, Visible v → Banded v) :
    ∀ ⦃v : Branch⦄, Visible v →
      LocallyNonempty v ∧ LocallyIsomorphic v ∧ Banded v :=
  paper_gluing_failure_component_gerbe_decomposition
    Visible LocallyNonempty LocallyIsomorphic Banded hNonempty hIso hBanded

end Omega.Topos
