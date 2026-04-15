namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the theorem asserting that every visible
    branch component is a banded gerbe.
    thm:component-gerbe-decomposition -/
theorem paper_gluing_failure_component_gerbe_decomposition
    {Branch : Type}
    (Visible : Branch → Prop)
    (LocallyNonempty : Branch → Prop)
    (LocallyIsomorphic : Branch → Prop)
    (Banded : Branch → Prop)
    (hNonempty : ∀ ⦃v : Branch⦄, Visible v → LocallyNonempty v)
    (hIso : ∀ ⦃v : Branch⦄, Visible v → LocallyIsomorphic v)
    (hBanded : ∀ ⦃v : Branch⦄, Visible v → Banded v) :
    ∀ ⦃v : Branch⦄, Visible v →
      LocallyNonempty v ∧ LocallyIsomorphic v ∧ Banded v := by
  intro v hv
  exact ⟨hNonempty hv, hIso hv, hBanded hv⟩

end Omega.Topos
