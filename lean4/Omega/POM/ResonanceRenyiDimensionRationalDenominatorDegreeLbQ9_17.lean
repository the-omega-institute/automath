import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-renyi-dimension-rational-denominator-degree-lb-q9-17`.
The arithmetic core of the resonance-window denominator bound: if a degree is at most `2 * b`,
then `b` is at least the integer ceiling of half that degree, written `(deg + 1) / 2`. -/
theorem paper_pom_renyi_dimension_rational_denominator_degree_lb_q9_17 {q deg b : ℕ}
    (hq : 9 ≤ q ∧ q ≤ 17) (hb : 1 ≤ b) (hfield : deg ≤ 2 * b) :
    b ≥ (deg + 1) / 2 := by
  have _ := hq
  have _ := hb
  omega

end Omega.POM
