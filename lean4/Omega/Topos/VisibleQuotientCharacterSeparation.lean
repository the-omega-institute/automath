namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for character separation of the visible quotient.
    cor:visible-quotient-character-separation -/
theorem paper_gluing_failure_visible_quotient_character_separation
    {A AVis Char Value : Type}
    (π : A → AVis)
    (eval : Char → A → Value)
    (Admissible : Char → Prop)
    (hFactor :
      ∀ ψ, Admissible ψ → ∃ ψbar : AVis → Value, ∀ a, eval ψ a = ψbar (π a))
    (hSeparate :
      ∀ ⦃x y : A⦄, π x ≠ π y → ∃ ψ, Admissible ψ ∧ eval ψ x ≠ eval ψ y) :
    ∀ x y : A, π x = π y ↔ ∀ ψ, Admissible ψ → eval ψ x = eval ψ y := by
  intro x y
  constructor
  · intro hπ ψ hψ
    rcases hFactor ψ hψ with ⟨ψbar, hbar⟩
    rw [hbar x, hbar y, hπ]
  · intro hChars
    classical
    by_cases hπ : π x = π y
    · exact hπ
    · rcases hSeparate hπ with ⟨ψ, hψ, hneq⟩
      exact False.elim (hneq (hChars ψ hψ))

end Omega.Topos
