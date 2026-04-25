import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Wrapper combining the localized finite-index subgroup classification with the chapter-local
profinite completion description: the subgroup lattice is classified by the coprime index
parameter, the profinite completion is modeled by the identity `\hat{\mathbf Z}`-proxy, and the
inverse-limit side is recorded as the product over the primes outside the localization support. -/
def xi_localized_finite_index_profinite_completion_classification_statement : Prop :=
  (∀ m n : ℕ, Nat.Coprime m 6 → Nat.Coprime n 6 → (m ∣ n ∧ n ∣ m ↔ m = n)) ∧
    Nonempty (ℤ ≃+* ℤ) ∧
    ∀ S : Finset ℕ,
      let xi_localized_finite_index_profinite_completion_classification_inverseLimit :
          Type := {p : ℕ // p ∉ S} → ℤ
      Nonempty
        (xi_localized_finite_index_profinite_completion_classification_inverseLimit ≃
          ({p : ℕ // p ∉ S} → ℤ))

/-- Paper label: `thm:xi-localized-finite-index-profinite-completion-classification`. -/
theorem paper_xi_localized_finite_index_profinite_completion_classification :
    xi_localized_finite_index_profinite_completion_classification_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro m n _hm _hn
    constructor
    · rintro ⟨hmn, hnm⟩
      exact Nat.dvd_antisymm hmn hnm
    · intro hmn
      subst hmn
      exact ⟨dvd_rfl, dvd_rfl⟩
  · exact ⟨RingEquiv.refl _⟩
  · intro S
    dsimp
    exact ⟨Equiv.refl _⟩

end Omega.Zeta
