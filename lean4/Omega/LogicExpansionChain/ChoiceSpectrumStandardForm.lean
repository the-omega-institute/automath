import Mathlib.Data.Set.Function
import Mathlib.Data.Setoid.Basic

namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Paper-facing quotient normal form for the choice spectrum:
    quotienting actions by equality of their future-image sets is equivalent to the
    range of the future-image map itself.
    prop:logic-expansion-choice-spectrum-standard-form -/
noncomputable def paper_logic_expansion_choice_spectrum_standard_form {Action Future : Type}
    (Gamma : Action → Set Future) : Quotient (Setoid.ker Gamma) ≃ Set.range Gamma := by
  refine Equiv.ofBijective
    (Quotient.lift (fun a => ⟨Gamma a, a, rfl⟩) (fun a b h => ?_)) ?_
  · exact Subtype.ext h
  · constructor
    · intro q₁ q₂ hq
      refine Quotient.inductionOn₂ q₁ q₂ ?_ hq
      intro a b hab
      exact Quotient.sound (by simpa using congrArg Subtype.val hab)
    · intro y
      rcases y with ⟨s, ⟨a, rfl⟩⟩
      exact ⟨Quotient.mk _ a, rfl⟩

end Omega.LogicExpansionChain
