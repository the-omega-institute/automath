import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-resonance-linear-disjointness-q14-15`. -/
theorem paper_pom_resonance_linear_disjointness_q14_15
    (discSquareclassIndependence q14GaloisS13 q15GaloisS11 q14q15TrivialIntersection
      q14q15ProductGalois : Prop)
    (hintersection : discSquareclassIndependence → q14q15TrivialIntersection)
    (hproduct :
      q14q15TrivialIntersection → q14GaloisS13 → q15GaloisS11 → q14q15ProductGalois)
    (hdisc : discSquareclassIndependence) (h14 : q14GaloisS13) (h15 : q15GaloisS11) :
    q14q15TrivialIntersection ∧ q14q15ProductGalois := by
  have htrivial : q14q15TrivialIntersection := hintersection hdisc
  exact ⟨htrivial, hproduct htrivial h14 h15⟩

end Omega.POM
