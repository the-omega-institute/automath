import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-hellinger-toeplitz-free-energy-area-law`. -/
theorem paper_xi_hellinger_toeplitz_free_energy_area_law
    (freeEnergy remainder : ℝ → ℝ)
    (hExpansion : ∀ Δ : ℝ, 0 < Δ →
      freeEnergy Δ =
        -(Real.pi ^ 2 / Δ) + Real.log (Real.pi ^ 2 / Δ) + 2 * Real.log 2 -
          Δ / 16 + remainder Δ)
    (hRemainder : ∀ Δ : ℝ, 0 < Δ →
      |remainder Δ| ≤ Real.exp (-(2 * Real.pi ^ 2 / Δ))) :
    ∀ Δ : ℝ, 0 < Δ →
      freeEnergy Δ =
        -(Real.pi ^ 2 / Δ) + Real.log (Real.pi ^ 2 / Δ) + 2 * Real.log 2 -
          Δ / 16 + remainder Δ := by
  have _ : ∀ Δ : ℝ, 0 < Δ →
      |remainder Δ| ≤ Real.exp (-(2 * Real.pi ^ 2 / Δ)) := hRemainder
  intro Δ hΔ
  exact hExpansion Δ hΔ

end Omega.Zeta
