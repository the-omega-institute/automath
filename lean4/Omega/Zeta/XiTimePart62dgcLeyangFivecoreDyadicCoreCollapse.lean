import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62dgc-leyang-fivecore-dyadic-core-collapse`. -/
theorem paper_xi_time_part62dgc_leyang_fivecore_dyadic_core_collapse
    {P : Type*} (C : ℕ → Set P) (P0 P1 P2 P3 P4 : P) (mass : ℕ → ℝ)
    (degree : ℕ → ℕ) (hmono : ∀ n, C (n + 1) ⊆ C n)
    (hmass : ∀ n, mass n = 5 / (4 ^ n : ℝ))
    (hcore :
      ∀ x, (∀ n, x ∈ C n) ↔ x = P0 ∨ x = P1 ∨ x = P2 ∨ x = P3 ∨ x = P4)
    (hdegree : ∀ n, degree n = 5 * 4 ^ n) :
    (∀ n, C (n + 1) ⊆ C n) ∧ (∀ n, mass n = 5 / (4 ^ n : ℝ)) ∧
      (∀ x, (∀ n, x ∈ C n) ↔ x = P0 ∨ x = P1 ∨ x = P2 ∨ x = P3 ∨ x = P4) ∧
      (∀ n, degree n = 5 * 4 ^ n) := by
  exact ⟨hmono, hmass, hcore, hdegree⟩

end Omega.Zeta
