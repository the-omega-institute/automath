import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-eps-distance-lawvere`. The reflexivity certificate and additive
composition certificate for the budget distance are exactly the two Lawvere-distance axioms. -/
theorem paper_pom_eps_distance_lawvere {W : Type*} (d : W -> W -> Real)
    (refl : forall w, d w w = 0)
    (triangle : forall w1 w2 w3, d w1 w3 <= d w1 w2 + d w2 w3) :
    (forall w, d w w = 0) /\
      (forall w1 w2 w3, d w1 w3 <= d w1 w2 + d w2 w3) := by
  exact ⟨refl, triangle⟩

end Omega.POM
