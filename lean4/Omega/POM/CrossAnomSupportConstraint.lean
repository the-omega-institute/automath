import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-cross-anom-support-constraint`.  If a configuration has a trivial
coordinate, the cross-anomaly contribution vanishes by the supplied cancellation principle. -/
theorem paper_pom_cross_anom_support_constraint {Index Character Theta : Type}
    (Delta : (Index → Prop) → (Index → Character) → Theta → Int)
    (trivial : Index → Character)
    (hasTrivialCoordinate : (Index → Prop) → (Index → Character) → Prop)
    (pairCancellation : ∀ S chi theta, hasTrivialCoordinate S chi → Delta S chi theta = 0)
    (S : Index → Prop) (chi : Index → Character) (theta : Theta)
    (h : hasTrivialCoordinate S chi) :
    Delta S chi theta = 0 := by
  let _trivialCoordinate := trivial
  exact pairCancellation S chi theta h

end Omega.POM
