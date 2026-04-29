import Mathlib

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-choice-spectrum-terminal-quotient-property`. Any readout that is
constant on equal future-image classes factors uniquely through the quotient by that relation. -/
theorem paper_conclusion_choice_spectrum_terminal_quotient_property {Action Future Y : Type*}
    (Γ : Action → Future) (F : Action → Y) (hF : ∀ a b, Γ a = Γ b → F a = F b) :
    ∃! Fbar : Quot (fun a b : Action => Γ a = Γ b) → Y, ∀ a, Fbar (Quot.mk _ a) = F a := by
  let Fbar : Quot (fun a b : Action => Γ a = Γ b) → Y :=
    Quot.lift F (fun a b hab => hF a b hab)
  refine ⟨Fbar, ?_, ?_⟩
  · intro a
    rfl
  · intro G hG
    funext q
    refine Quot.inductionOn q ?_
    intro a
    simpa [Fbar] using hG a

end Omega.Conclusion
