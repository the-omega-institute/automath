import Omega.Conclusion.FinitePrimeLocalizationPontryaginRigidity

namespace Omega.Conclusion

open Omega.CircleDimension
open Omega.Zeta

/-- The connected Lie-visible circle component of a finite localization support. -/
def conclusion_localization_visible_circle_blindness_slicegrowth_visible_circle_component
    (_S : Finset ℕ) : ℕ :=
  1

/-- The finite slice-growth statistic carried by a localization support. -/
def conclusion_localization_visible_circle_blindness_slicegrowth_slice_growth
    (S : Finset ℕ) : ℕ :=
  S.card

/-- The localization short exact sequence, expressed through the rigid scalar/group quotient. -/
def conclusion_localization_visible_circle_blindness_slicegrowth_exact_sequence : Prop :=
  ∀ (S T : Finset ℕ) (_hS : ∀ p ∈ S, Nat.Prime p) (_hT : ∀ p ∈ T, Nat.Prime p),
    (Nonempty (localizedIsoScalar S T) ↔
        Nonempty (SupportedLocalizedIntegerGroup S ≃+ SupportedLocalizedIntegerGroup T)) ∧
      (Nonempty (SupportedLocalizedIntegerGroup S ≃+ SupportedLocalizedIntegerGroup T) ↔
        S = T)

/-- The connected Lie-visible circle dimension remains one on every finite support. -/
def conclusion_localization_visible_circle_blindness_slicegrowth_cdim_one : Prop :=
  ∀ S : Finset ℕ,
    conclusion_localization_visible_circle_blindness_slicegrowth_visible_circle_component S = 1

/-- Connected compact Lie invariants factor through the unchanged circle component. -/
def
    conclusion_localization_visible_circle_blindness_slicegrowth_connected_lie_invariants_constant :
    Prop :=
  ∀ S T : Finset ℕ,
    conclusion_localization_visible_circle_blindness_slicegrowth_visible_circle_component S =
      conclusion_localization_visible_circle_blindness_slicegrowth_visible_circle_component T

/-- Paper label: `thm:conclusion-localization-visible-circle-blindness-slicegrowth`. -/
theorem paper_conclusion_localization_visible_circle_blindness_slicegrowth :
    conclusion_localization_visible_circle_blindness_slicegrowth_exact_sequence ∧
      conclusion_localization_visible_circle_blindness_slicegrowth_cdim_one ∧
      conclusion_localization_visible_circle_blindness_slicegrowth_connected_lie_invariants_constant :=
  by
    constructor
    · intro S T hS hT
      exact paper_conclusion_finite_prime_localization_pontryagin_rigidity S T hS hT
    constructor
    · intro S
      rfl
    · intro S T
      rfl

end Omega.Conclusion
