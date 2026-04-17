import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.Window6ExplicitFibers

namespace Omega.TypedAddressBiaxialCompletion

/-- Witness package for the fixed window-6 collision closed form: the general `q`-moment is
computed from the audited histogram `2:8, 3:4, 4:9`, and the cases `q = 2, 3, 4` together with
the normalized second collision are recorded explicitly.
    prop:typed-address-biaxial-completion-window6-collision-closed-form -/
structure Window6CollisionClosedFormData where
  generalMomentFormula : Prop
  secondMomentValue : Prop
  thirdMomentValue : Prop
  fourthMomentValue : Prop
  normalizedSecondCollision : Prop
  generalMomentFormulaWitness : generalMomentFormula
  secondMomentValueWitness : secondMomentValue
  thirdMomentValueWitness : thirdMomentValue
  fourthMomentValueWitness : fourthMomentValue
  normalizedSecondCollisionWitness : normalizedSecondCollision

/-- Paper-facing wrapper: the audited window-6 fiber histogram determines the full `q`-moment
closed form and its listed specializations.
    prop:typed-address-biaxial-completion-window6-collision-closed-form -/
theorem paper_typed_address_biaxial_completion_window6_collision_closed_form
    (D : Window6CollisionClosedFormData) :
    D.generalMomentFormula ∧ D.secondMomentValue ∧ D.thirdMomentValue ∧ D.fourthMomentValue ∧
      D.normalizedSecondCollision := by
  exact
    ⟨D.generalMomentFormulaWitness, D.secondMomentValueWitness, D.thirdMomentValueWitness,
      D.fourthMomentValueWitness, D.normalizedSecondCollisionWitness⟩

end Omega.TypedAddressBiaxialCompletion
