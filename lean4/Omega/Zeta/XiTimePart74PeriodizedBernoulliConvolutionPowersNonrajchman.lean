import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part74-periodized-bernoulli-convolution-powers-nonrajchman`. -/
theorem paper_xi_time_part74_periodized_bernoulli_convolution_powers_nonrajchman
    (a : ℕ → ℝ) (c : ℝ) (r : ℕ) (hr : 1 ≤ r) (hc : 0 < c)
    (hlim : Filter.Tendsto a Filter.atTop (nhds c)) :
    Filter.Tendsto (fun m => a m ^ r) Filter.atTop (nhds (c ^ r)) ∧ 0 < c ^ r ∧
      ¬ Filter.Tendsto (fun m => a m ^ r) Filter.atTop (nhds 0) := by
  let _ := hr
  have hpow : Filter.Tendsto (fun m => a m ^ r) Filter.atTop (nhds (c ^ r)) := by
    exact hlim.pow r
  have hpos : 0 < c ^ r := pow_pos hc r
  refine ⟨hpow, hpos, ?_⟩
  intro hzero
  have huniq : c ^ r = 0 := tendsto_nhds_unique hpow hzero
  exact hpos.ne' huniq

end Omega.Zeta
