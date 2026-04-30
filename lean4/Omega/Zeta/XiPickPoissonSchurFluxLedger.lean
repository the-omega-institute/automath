import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- In the diagonal Pick--Poisson model the leading-principal determinant is the product of
the one-step conditional Schur fluxes. -/
noncomputable def xi_pick_poisson_schur_flux_ledger_diagonalDet
    (kappa : ℕ) (p : Fin kappa → ℝ) : ℝ :=
  ∏ m, p m

/-- The diagonal model has conditional flux equal to the newly added diagonal entry. -/
def xi_pick_poisson_schur_flux_ledger_schurFlux
    {kappa : ℕ} (p : Fin kappa → ℝ) (m : Fin kappa) : ℝ :=
  p m

/-- Concrete Schur-flux ledger statement for the positive diagonal chain. -/
def xi_pick_poisson_schur_flux_ledger_statement : Prop :=
  ∀ (kappa : ℕ) (p : Fin kappa → ℝ),
    (∀ m, 0 < p m) →
      xi_pick_poisson_schur_flux_ledger_diagonalDet kappa p =
          ∏ m, xi_pick_poisson_schur_flux_ledger_schurFlux p m ∧
        (∀ m, 0 < xi_pick_poisson_schur_flux_ledger_schurFlux p m) ∧
          ∀ m, xi_pick_poisson_schur_flux_ledger_schurFlux p m ≤ p m

/-- Paper label: `prop:xi-pick-poisson-schur-flux-ledger`. -/
theorem paper_xi_pick_poisson_schur_flux_ledger :
    xi_pick_poisson_schur_flux_ledger_statement := by
  intro kappa p hp
  refine ⟨?_, ?_, ?_⟩
  · simp [xi_pick_poisson_schur_flux_ledger_diagonalDet,
      xi_pick_poisson_schur_flux_ledger_schurFlux]
  · intro m
    simpa [xi_pick_poisson_schur_flux_ledger_schurFlux] using hp m
  · intro m
    simp [xi_pick_poisson_schur_flux_ledger_schurFlux]

end Omega.Zeta
