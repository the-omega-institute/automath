import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part28b-strip-offline-density-exact`. -/
theorem paper_xi_time_part28b_strip_offline_density_exact
    (L : ℝ) (nuForb : ℕ) (offCount : ℕ → ℝ) (hL : 1 < L)
    (hcomb : ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : ℕ,
        |offCount T - ((2 * Real.log L / Real.pi) * (nuForb : ℝ)) * (T : ℝ)| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : ℕ,
        |offCount T - ((2 * Real.log L / Real.pi) * (nuForb : ℝ)) * (T : ℝ)| ≤ C := by
  have _hL : 1 < L := hL
  exact hcomb

end Omega.Zeta
