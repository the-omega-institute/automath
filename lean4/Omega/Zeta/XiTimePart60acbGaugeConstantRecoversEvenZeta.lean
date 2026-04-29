import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Filter
open scoped Topology

/-- Paper label: `thm:xi-time-part60acb-gauge-constant-recovers-even-zeta`. -/
theorem paper_xi_time_part60acb_gauge_constant_recovers_even_zeta
    (B zeta : ℕ → ℝ) (scaled : ℕ → ℕ → ℝ) (gamma prefactor : ℕ → ℝ)
    (hgamma : ∀ r, 1 ≤ r → gamma r ≠ 0)
    (hscaled : ∀ r, 1 ≤ r → Tendsto (scaled r) atTop (𝓝 (gamma r * B (2 * r))))
    (hzeta : ∀ r, 1 ≤ r → zeta (2 * r) = prefactor r * B (2 * r)) :
    ∀ r, 1 ≤ r →
      Tendsto (fun m => scaled r m / gamma r) atTop (𝓝 (B (2 * r))) ∧
        zeta (2 * r) = prefactor r * B (2 * r) := by
  intro r hr
  constructor
  · have hlim := (hscaled r hr).div_const (gamma r)
    have htarget : gamma r * B (2 * r) / gamma r = B (2 * r) := by
      field_simp [hgamma r hr]
    simpa [htarget] using hlim
  · exact hzeta r hr

end Omega.Zeta
