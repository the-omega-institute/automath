import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic

namespace Omega.Zeta

open Filter
open scoped Topology

/-- Paper label: `thm:xi-time-part66-shannon-gap-times-M-diverges`.
If the Pinsker/l1-l2 comparison gives the Shannon-gap lower bound
`(1 / 2) * (M * collision - 1) ≤ M * gap` eventually, then the already verified
collision-scale divergence transfers to the Shannon gap at scale `M`. -/
theorem paper_xi_time_part66_shannon_gap_times_m_diverges
    (M collision shannonGap : ℕ → ℝ)
    (hcollision :
      Tendsto (fun m : ℕ => M m * collision m - 1) atTop atTop)
    (hPinsker :
      ∀ᶠ m in atTop,
        (1 / 2 : ℝ) * (M m * collision m - 1) ≤ M m * shannonGap m) :
    Tendsto (fun m : ℕ => M m * shannonGap m) atTop atTop := by
  have hhalf :
      Tendsto (fun m : ℕ => (1 / 2 : ℝ) * (M m * collision m - 1)) atTop atTop := by
    exact hcollision.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  exact tendsto_atTop_mono' atTop hPinsker hhalf

end Omega.Zeta
