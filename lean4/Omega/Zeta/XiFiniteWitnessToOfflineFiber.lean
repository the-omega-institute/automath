import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-finite-witness-to-offline-fiber`. -/
theorem paper_xi_finite_witness_to_offline_fiber
    (κ : ℕ) (toeplitzFails : Prop) (candidatePoint depth gamma offlineFiber : Fin κ → ℂ)
    (hκ : toeplitzFails → 1 ≤ κ)
    (hfiber : ∀ j, offlineFiber j = (1 / 2 : ℂ) + Complex.I * gamma j - depth j) :
    toeplitzFails →
      1 ≤ κ ∧ ∀ j, offlineFiber j = (1 / 2 : ℂ) + Complex.I * gamma j - depth j := by
  have _candidatePoint_available := candidatePoint
  intro hfail
  exact ⟨hκ hfail, hfiber⟩

end Omega.Zeta
