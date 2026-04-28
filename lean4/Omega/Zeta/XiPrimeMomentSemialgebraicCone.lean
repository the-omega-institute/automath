import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Zeta

/-- Paper label: `thm:xi-prime-moment-semialgebraic-cone`. A fixed-level Toeplitz PSD condition
can be re-expressed as the corresponding finite family of prime-moment polynomial inequalities
once the finite reduction interface has been supplied. -/
theorem paper_xi_prime_moment_semialgebraic_cone (N K : ℕ)
    (toeplitzPSD primeMomentPolynomialInequalities : Prop)
    (hFiniteReduction : toeplitzPSD ↔ primeMomentPolynomialInequalities) :
    ∃ K_N : ℕ, K_N = K ∧ (toeplitzPSD ↔ primeMomentPolynomialInequalities) := by
  exact ⟨K, rfl, hFiniteReduction⟩

end Omega.Zeta
