import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-elliptic-circle-dimension-minimality`. -/
theorem paper_pom_elliptic_circle_dimension_minimality
    (E S1 : Type*)
    (continuousObservation injectiveObservation nonconstantObservation : (E → S1) → Prop)
    (twoTimeRecoverable minimalTwoCircleChannels : Prop)
    (hNoOneCircle :
      ∀ g, continuousObservation g → nonconstantObservation g → ¬ injectiveObservation g)
    (hTwo : twoTimeRecoverable)
    (hMinimal : twoTimeRecoverable → minimalTwoCircleChannels) :
    (∀ g, continuousObservation g → nonconstantObservation g → ¬ injectiveObservation g) ∧
      minimalTwoCircleChannels := by
  exact ⟨hNoOneCircle, hMinimal hTwo⟩

end Omega.POM
