import Mathlib.Tactic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

namespace Omega.Conclusion.CycleRankSaturation

open Filter Topology

/-- Squeeze to 1: if `1 - ε n ≤ x n ≤ 1` and `ε → 0`, then `x → 1`.
    cor:conclusion-boundary-cycle-rank-saturation -/
theorem squeeze_to_one (x ε : ℕ → ℝ)
    (hlo : ∀ n, 1 - ε n ≤ x n)
    (hhi : ∀ n, x n ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 1) := by
  have hlo' : Tendsto (fun n => 1 - ε n) atTop (𝓝 1) := by
    have : Tendsto (fun n => 1 - ε n) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hε
    simp at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo' tendsto_const_nhds hlo hhi

/-- Cycle rank saturation: `r/A → 1` when `X/A → 0`.
    cor:conclusion-boundary-cycle-rank-saturation -/
theorem paper_conclusion_boundary_cycle_rank_saturation
    (r A X c : ℕ → ℝ)
    (hA_pos : ∀ n, 0 < A n)
    (hrank : ∀ n, r n = A n - X n + c n)
    (hc_bound : ∀ n, 0 ≤ c n ∧ c n ≤ X n)
    (_hX_nn : ∀ n, 0 ≤ X n)
    (hXA : Tendsto (fun n => X n / A n) atTop (𝓝 0)) :
    Tendsto (fun n => r n / A n) atTop (𝓝 1) := by
  apply squeeze_to_one _ (fun n => X n / A n)
  · -- Lower bound: 1 - X/A ≤ r/A
    intro n
    have hA := hA_pos n
    have hr := hrank n
    have hc := hc_bound n
    rw [hr]
    rw [le_div_iff₀ hA]
    have : (1 - X n / A n) * A n = A n - X n := by
      field_simp
    rw [this]
    linarith [hc.1]
  · -- Upper bound: r/A ≤ 1
    intro n
    have hA := hA_pos n
    have hr := hrank n
    have hc := hc_bound n
    rw [div_le_one₀ hA, hr]
    linarith [hc.1, _hX_nn n]
  · exact hXA

end Omega.Conclusion.CycleRankSaturation
