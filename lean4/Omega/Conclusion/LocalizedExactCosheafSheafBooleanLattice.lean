import Mathlib.Tactic
import Omega.Conclusion.LocalizedGroupsMayerVietoris

namespace Omega.Conclusion

open Omega.CircleDimension.LocalizedGsEmbeddingOrderData

/-- Paper label: `thm:conclusion-localized-exact-cosheaf-sheaf-boolean-lattice`.
On finite prime supports, the localized groups form an exact cosheaf under unions and
intersections, and Pontryagin duality records the corresponding exact sheaf statement using the
same concrete Mayer-Vietoris datum. -/
theorem paper_conclusion_localized_exact_cosheaf_sheaf_boolean_lattice
    (S T : Finset ℕ) (hSum : localizedMayerVietorisSurjective S T) :
    (∀ q : ℚ, inLocalizedGs (S ∪ T) q →
      ∃ a b : ℚ, inLocalizedGs S a ∧ inLocalizedGs T b ∧ localizedCodiagonal (a, b) = q) ∧
      (∀ a b : ℚ, inLocalizedGs S a → inLocalizedGs T b →
        localizedCodiagonal (a, b) = 0 →
        ∃ x : ℚ, inLocalizedGs (S ∩ T) x ∧ localizedDiagonal S T x = (a, b)) ∧
      (∀ q : ℚ, (inLocalizedGs S q ∧ inLocalizedGs T q) ↔ inLocalizedGs (S ∩ T) q) ∧
      localizedPontryaginDualExact S T := by
  rcases paper_conclusion_localized_groups_mayer_vietoris S T hSum with
    ⟨hInter, hKernel, hCosheaf, hSheaf⟩
  exact ⟨hCosheaf, hKernel, hInter, hSheaf⟩

end Omega.Conclusion
