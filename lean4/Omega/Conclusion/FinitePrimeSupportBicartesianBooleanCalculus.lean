import Mathlib.Tactic
import Omega.Conclusion.LocalizedGroupsMayerVietoris

namespace Omega.Conclusion

open Omega.CircleDimension.LocalizedGsEmbeddingOrderData

/-- Pullback side of the Boolean localization square:
`G_{S ∩ T} = G_S ×_{G_{S ∪ T}} G_T` inside `ℚ`. -/
def finitePrimeSupportPullback (S T : Finset ℕ) : Prop :=
  ∀ q : ℚ, (inLocalizedGs S q ∧ inLocalizedGs T q) ↔ inLocalizedGs (S ∩ T) q

/-- Kernel description for the diagonal/codiagonal Mayer-Vietoris square. -/
def finitePrimeSupportKernel (S T : Finset ℕ) : Prop :=
  ∀ a b : ℚ, inLocalizedGs S a → inLocalizedGs T b →
    localizedCodiagonal (a, b) = 0 →
    ∃ x : ℚ, inLocalizedGs (S ∩ T) x ∧ localizedDiagonal S T x = (a, b)

/-- Pushout side of the Mayer-Vietoris square. -/
def finitePrimeSupportPushout (S T : Finset ℕ) : Prop :=
  localizedMayerVietorisSurjective S T

/-- Bicartesian Boolean calculus for finite prime supports: the localization square is both a
pullback and a pushout, and the Pontryagin-dual exact sequence carries the same concrete data. -/
def finitePrimeSupportBicartesianBooleanCalculus (S T : Finset ℕ) : Prop :=
  finitePrimeSupportPullback S T ∧
    finitePrimeSupportKernel S T ∧
    finitePrimeSupportPushout S T ∧
    localizedPontryaginDualExact S T

/-- Paper label: `thm:conclusion-finite-primesupport-bicartesian-boolean-calculus`. -/
theorem paper_conclusion_finite_primesupport_bicartesian_boolean_calculus
    (S T : Finset ℕ) (hSum : localizedMayerVietorisSurjective S T) :
    finitePrimeSupportBicartesianBooleanCalculus S T := by
  rcases paper_conclusion_localized_groups_mayer_vietoris S T hSum with
    ⟨hPullback, hKernel, hPushout, hDual⟩
  exact ⟨hPullback, hKernel, hPushout, hDual⟩

end Omega.Conclusion
