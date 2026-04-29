import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-reversekl-extremal-gap-energy-correction`. -/
theorem paper_xi_reversekl_extremal_gap_energy_correction
    (H ar r Er : ℝ)
    (hbound :
      H ≤ -Real.log (1 - r ^ 2) - ar ^ 2 * (r ^ 2 / (1 - r ^ 2) - Er / 2))
    (hnonneg : 0 ≤ r ^ 2 / (1 - r ^ 2) - Er / 2) :
    H ≤ -Real.log (1 - r ^ 2) - ar ^ 2 * (r ^ 2 / (1 - r ^ 2) - Er / 2) ∧
      0 ≤ r ^ 2 / (1 - r ^ 2) - Er / 2 := by
  exact ⟨hbound, hnonneg⟩

end Omega.Zeta
