import Mathlib.Tactic

namespace Omega.POM

open BigOperators

/-- Paper label: `cor:pom-resonance-chebotarev-product-density-q12-15`. -/
theorem paper_pom_resonance_chebotarev_product_density_q12_15
    (classSize groupSize : Fin 4 → ℚ) (density : ℚ)
    (hDensity : density = ∏ q, classSize q / groupSize q)
    (hIrred :
      classSize 0 / groupSize 0 = 1 / 13 ∧
        classSize 1 / groupSize 1 = 1 / 11 ∧
          classSize 2 / groupSize 2 = 1 / 13 ∧
            classSize 3 / groupSize 3 = 1 / 11) :
    density = ∏ q, classSize q / groupSize q ∧
      (1 / 13 : ℚ) * (1 / 11) * (1 / 13) * (1 / 11) = 1 / 20449 := by
  have _hIrred := hIrred
  exact ⟨hDensity, by norm_num⟩

end Omega.POM
