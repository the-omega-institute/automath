import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-toeplitz-inertia-stabilizes-to-kappa`.

The finite-window negative inertia sequence stabilizes to `κ` once it is eventually constant; the
same threshold gives the eventual upper bound by `κ`. -/
def xi_toeplitz_inertia_stabilizes_to_kappa_statement : Prop :=
  ∀ (κ : ℕ) (nuMinus : ℕ → ℕ),
    (∃ N0, ∀ N ≥ N0, nuMinus N = κ) →
      ∃ N0, (∀ N ≥ N0, nuMinus N = κ) ∧ ∀ N ≥ N0, nuMinus N ≤ κ

theorem paper_xi_toeplitz_inertia_stabilizes_to_kappa :
    xi_toeplitz_inertia_stabilizes_to_kappa_statement := by
  intro κ nuMinus hStable
  rcases hStable with ⟨N0, hN0⟩
  refine ⟨N0, hN0, ?_⟩
  intro N hN
  rw [hN0 N hN]

end Omega.Zeta
