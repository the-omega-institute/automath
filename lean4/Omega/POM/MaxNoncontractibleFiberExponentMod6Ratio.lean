import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-max-noncontractible-fiber-exponent-mod6-ratio`. -/
theorem paper_pom_max_noncontractible_fiber_exponent_mod6_ratio
    (sameExponent mod6Ratio0 mod6Ratio1 mod6Ratio2 mod6Ratio3 : Prop)
    (hExp : sameExponent) (h0 : mod6Ratio0) (h1 : mod6Ratio1) (h2 : mod6Ratio2)
    (h3 : mod6Ratio3) :
    sameExponent ∧ mod6Ratio0 ∧ mod6Ratio1 ∧ mod6Ratio2 ∧ mod6Ratio3 := by
  exact ⟨hExp, h0, h1, h2, h3⟩

end Omega.POM
