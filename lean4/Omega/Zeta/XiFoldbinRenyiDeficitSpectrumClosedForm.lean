import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-foldbin-renyi-deficit-spectrum-closed-form`. -/
theorem paper_xi_foldbin_renyi_deficit_spectrum_closed_form
    (α : ℕ) (hα : (α : ℝ) ≠ 1) (φ r0 r1 : ℝ) (hφ0 : φ ≠ 0)
    (hr0 : r0 = φ ^ 2 / Real.sqrt 5) (hr1 : r1 = φ / Real.sqrt 5) :
    (1 / ((α : ℝ) - 1)) * Real.log ((1 / φ) * r0 ^ α + (1 / φ ^ 2) * r1 ^ α) =
      (1 / ((α : ℝ) - 1)) *
        Real.log ((1 / φ) * (φ ^ 2 / Real.sqrt 5) ^ α +
          (1 / φ ^ 2) * (φ / Real.sqrt 5) ^ α) := by
  have _ := hα
  have _ := hφ0
  rw [hr0, hr1]

end Omega.Zeta
