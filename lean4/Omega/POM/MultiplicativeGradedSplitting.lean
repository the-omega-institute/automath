import Mathlib.Tactic

namespace Omega

/-- Paper label: `thm:xi-time-part79-pom-multiplicative-graded-splitting`. -/
theorem paper_xi_time_part79_pom_multiplicative_graded_splitting
    {Word Class NormalForm Anom : Type*} (Q : Word → ℕ) (nf : Word → NormalForm)
    (anom : Word → Anom) (repr : Class → Word) (classOf : Word → Class)
    (hclass : ∀ w₁ w₂,
      classOf w₁ = classOf w₂ ↔ Q w₁ = Q w₂ ∧ nf w₁ = nf w₂ ∧ anom w₁ = anom w₂)
    (hrepr : ∀ C, classOf (repr C) = C) :
    (∀ C, ∃ q N A, Q (repr C) = q ∧ nf (repr C) = N ∧ anom (repr C) = A) ∧
      (∀ w₁ w₂,
        classOf w₁ = classOf w₂ ↔ Q w₁ = Q w₂ ∧ nf w₁ = nf w₂ ∧ anom w₁ = anom w₂) := by
  have _ := hrepr
  refine ⟨?_, hclass⟩
  intro C
  exact ⟨Q (repr C), nf (repr C), anom (repr C), rfl, rfl, rfl⟩

end Omega
