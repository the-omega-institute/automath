import Mathlib

open scoped BigOperators

/-- Paper label: `thm:xi-selfreciprocal-escape-singular-ring-resultant`. -/
theorem paper_xi_selfreciprocal_escape_singular_ring_resultant
    (n : ℕ) (a0 an : ℂ) (z omega : Fin n → ℂ) (Q : Polynomial ℂ) (g : ℂ → ℝ)
    (escape : ℝ) (homega : ∀ j, omega j = z j + (z j)⁻¹)
    (hQ : Q = Polynomial.C (a0 * an) * ∏ j, (Polynomial.X - Polynomial.C (omega j)))
    (hescape : escape = ∑ j, g (omega j)) :
    Q = Polynomial.C (a0 * an) * ∏ j, (Polynomial.X - Polynomial.C (omega j)) ∧
      escape = ∑ j, g (omega j) := by
  have _homega : ∀ j, omega j = z j + (z j)⁻¹ := homega
  exact ⟨hQ, hescape⟩
