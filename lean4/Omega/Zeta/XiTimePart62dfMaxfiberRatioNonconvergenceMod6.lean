import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62df-maxfiber-ratio-nonconvergence-mod6`. -/
theorem paper_xi_time_part62df_maxfiber_ratio_nonconvergence_mod6 (a : ℕ → ℝ)
    (L0 L1 L2 L3 : ℝ) (h01 : L0 ≠ L1)
    (h0 : Tendsto (fun n : ℕ => a (6 * n)) atTop (𝓝 L0))
    (h1 : Tendsto (fun n : ℕ => a (6 * n + 1)) atTop (𝓝 L1))
    (h2 : Tendsto (fun n : ℕ => a (6 * n + 2)) atTop (𝓝 L2))
    (h3 : Tendsto (fun n : ℕ => a (6 * n + 3)) atTop (𝓝 L3)) :
    (¬ ∃ L : ℝ, Tendsto a atTop (𝓝 L)) ∧ ({L0, L1, L2, L3} : Set ℝ).Finite := by
  let _ := h2
  let _ := h3
  constructor
  · rintro ⟨L, hL⟩
    have h6 : Tendsto (fun n : ℕ => 6 * n) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨b, ?_⟩
      intro n hn
      exact le_trans hn (Nat.le_mul_of_pos_left n (by norm_num : 0 < 6))
    have h6p1 : Tendsto (fun n : ℕ => 6 * n + 1) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨b, ?_⟩
      intro n hn
      exact le_trans hn (Nat.le_trans (Nat.le_mul_of_pos_left n (by norm_num : 0 < 6))
        (Nat.le_add_right _ _))
    have hL0 : L0 = L := tendsto_nhds_unique h0 (hL.comp h6)
    have hL1 : L1 = L := tendsto_nhds_unique h1 (hL.comp h6p1)
    exact h01 (hL0.trans hL1.symm)
  · simp

end Omega.Zeta
