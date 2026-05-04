import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-fourier-joukowsky-character-compatibility`. -/
theorem paper_conclusion_fourier_joukowsky_character_compatibility
    {A : Type*} [CommSemiring A] (chi : A →+* ℂ) (L Δ : ℤ → A → A)
    (Lc Δc : ℤ → ℂ → ℂ) (x : A)
    (hL : ∀ k, chi (L k x) = Lc k (chi x))
    (hΔ : ∀ k, chi (Δ k x) = Δc k (chi x)) :
    (∀ k, chi (L k x) = Lc k (chi x)) ∧
      (∀ k, chi (Δ k x) = Δc k (chi x)) := by
  exact ⟨hL, hΔ⟩

end Omega.Conclusion
