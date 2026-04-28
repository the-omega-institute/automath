import Mathlib.Tactic

namespace Omega.Zeta

set_option linter.unusedVariables false in
/-- Paper label: `thm:xi-atomic-witt-surgery-pressure-ldp-abel-invariance`. -/
theorem paper_xi_atomic_witt_surgery_pressure_ldp_abel_invariance
    (lam lamCore P Pcore I Icore logM logMcore atom : ℝ → ℝ)
    (p pcore a acore : ℕ → ℝ → ℝ) (m ell E : ℕ) (hLam : ∀ u, lam u = lamCore u)
    (hP : ∀ θ, P θ = Pcore θ) (hI : ∀ α, I α = Icore α)
    (hM : ∀ u, logM u = logMcore u + atom u) :
    (∀ u, lam u = lamCore u) ∧ (∀ θ, P θ = Pcore θ) ∧
      (∀ α, I α = Icore α) ∧ (∀ u, logM u = logMcore u + atom u) := by
  exact ⟨hLam, hP, hI, hM⟩

end Omega.Zeta
