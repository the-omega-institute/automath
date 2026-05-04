import Mathlib.Tactic
import Omega.Zeta.XiLocalizedSolenoidPeriodicPointFormula

namespace Omega.Zeta

/-- Paper label: `thm:xi-localized-solenoid-fixedpoints-artin-mazur-series`. -/
theorem paper_xi_localized_solenoid_fixedpoints_artin_mazur_series
    (S : FinitePrimeLocalization) (a : ℕ) (ha : 2 ≤ a) :
    (∀ k : ℕ, 1 ≤ k →
      Nonempty
        (xi_localized_solenoid_periodic_point_formula_fixModel S a k ≃+
          ZMod (localizedIndex S (a ^ k - 1)))) ∧
      (∀ k : ℕ, 1 ≤ k →
        Nat.card (xi_localized_solenoid_periodic_point_formula_fixModel S a k) =
          localizedIndex S (a ^ k - 1)) ∧
      (S = ∅ → ∀ k : ℕ, 1 ≤ k →
        Nat.card (xi_localized_solenoid_periodic_point_formula_fixModel S a k) = a ^ k - 1) := by
  have _ha := ha
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    exact ⟨AddEquiv.refl _⟩
  · intro k hk
    exact Nat.card_zmod (localizedIndex S (a ^ k - 1))
  · intro hS k hk
    subst S
    simp [xi_localized_solenoid_periodic_point_formula_fixModel, localizedIndex, nSperp]

end Omega.Zeta
