import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-a2-benchmark`. The four audited `A₂` collision-kernel ingredients
combine into the advertised benchmark package. -/
theorem paper_pom_a2_benchmark
    (perronScale primitiveOrbitScale finitePartScale renyiGapQuantified : Prop)
    (hperron : perronScale) (hprimitive : primitiveOrbitScale) (hfinite : finitePartScale)
    (hrenyi : renyiGapQuantified) :
    perronScale ∧ primitiveOrbitScale ∧ finitePartScale ∧ renyiGapQuantified := by
  exact ⟨hperron, hprimitive, hfinite, hrenyi⟩

end Omega.POM
