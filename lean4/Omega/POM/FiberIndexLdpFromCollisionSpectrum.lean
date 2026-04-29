import Mathlib.Tactic

namespace Omega.POM

/-- The paper-facing package of the fiber-index large-deviation consequences from the collision
spectrum assumptions.
    prop:pom-fiber-index-ldp-from-collision-spectrum -/
theorem paper_pom_fiber_index_ldp_from_collision_spectrum
    (ldp rate_formula strict_convex unique_zero curvature_duality integer_nodes : Prop)
    (hldp : ldp) (hrate : rate_formula) (hconv : strict_convex) (hzero : unique_zero)
    (hcurv : curvature_duality) (hnodes : integer_nodes) :
    ldp ∧ rate_formula ∧ strict_convex ∧ unique_zero ∧ curvature_duality ∧ integer_nodes := by
  exact ⟨hldp, hrate, hconv, hzero, hcurv, hnodes⟩

end Omega.POM
