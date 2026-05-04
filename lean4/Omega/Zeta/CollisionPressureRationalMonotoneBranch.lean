import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9p-collision-pressure-rational-monotone-branch`. -/
theorem paper_xi_time_part9p_collision_pressure_rational_monotone_branch :
    let u := fun ρ : ℝ => ρ * (ρ ^ 2 - 2 * ρ - 1) / (ρ - 1)
    (∀ ρ : ℝ, 1 < ρ → (0 < u ρ ↔ 1 + Real.sqrt 2 < ρ)) ∧
      (∀ ρ : ℝ, 1 + Real.sqrt 2 < ρ →
        0 < (2 * ρ ^ 3 - 5 * ρ ^ 2 + 4 * ρ + 1) / (ρ - 1) ^ 2) ∧
      (∀ y : ℝ, 0 < y → ∃ ρ : ℝ, 1 + Real.sqrt 2 < ρ ∧ u ρ = y) := by
  classical
  let u := fun ρ : ℝ => ρ * (ρ ^ 2 - 2 * ρ - 1) / (ρ - 1)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_lt_two : Real.sqrt 2 < (2 : ℝ) := by
    nlinarith [hsqrt_sq, sq_nonneg (Real.sqrt 2)]
  refine ⟨?_, ?_, ?_⟩
  · intro ρ hρ
    have hρ_pos : 0 < ρ := by linarith
    have hden_pos : 0 < ρ - 1 := by linarith
    have hq_factor :
        ρ ^ 2 - 2 * ρ - 1 = (ρ - (1 + Real.sqrt 2)) * (ρ - (1 - Real.sqrt 2)) := by
      nlinarith [hsqrt_sq]
    have hright_factor_pos : 0 < ρ - (1 - Real.sqrt 2) := by
      nlinarith
    constructor
    · intro hu
      have hq_pos : 0 < ρ ^ 2 - 2 * ρ - 1 := by
        have hmul_pos : 0 < ρ * (ρ ^ 2 - 2 * ρ - 1) := by
          exact (div_pos_iff_of_pos_right hden_pos).1 (by simpa [u] using hu)
        exact (mul_pos_iff_of_pos_left hρ_pos).1 hmul_pos
      have hleft_pos : 0 < ρ - (1 + Real.sqrt 2) := by
        rw [hq_factor] at hq_pos
        exact (mul_pos_iff_of_pos_right hright_factor_pos).1 hq_pos
      linarith
    · intro hthreshold
      have hleft_pos : 0 < ρ - (1 + Real.sqrt 2) := by linarith
      have hq_pos : 0 < ρ ^ 2 - 2 * ρ - 1 := by
        rw [hq_factor]
        exact mul_pos hleft_pos hright_factor_pos
      exact div_pos (mul_pos hρ_pos hq_pos) hden_pos
  · intro ρ hρ
    have hρ_pos : 0 < ρ := by nlinarith [hsqrt_pos]
    have hden_ne : ρ - 1 ≠ 0 := by nlinarith [hsqrt_pos]
    have hden_sq_pos : 0 < (ρ - 1) ^ 2 := by
      exact sq_pos_of_ne_zero hden_ne
    have hq_pos : 0 < ρ ^ 2 - 2 * ρ - 1 := by
      have hright_pos : 0 < ρ - (1 - Real.sqrt 2) := by nlinarith
      have hleft_pos : 0 < ρ - (1 + Real.sqrt 2) := by linarith
      have hfactor :
          ρ ^ 2 - 2 * ρ - 1 = (ρ - (1 + Real.sqrt 2)) * (ρ - (1 - Real.sqrt 2)) := by
        nlinarith [hsqrt_sq]
      rw [hfactor]
      exact mul_pos hleft_pos hright_pos
    have hcoef_pos : 0 < 2 * ρ - 1 := by nlinarith [hsqrt_pos]
    have hnum_pos : 0 < 2 * ρ ^ 3 - 5 * ρ ^ 2 + 4 * ρ + 1 := by
      have hdecomp :
          2 * ρ ^ 3 - 5 * ρ ^ 2 + 4 * ρ + 1 =
            (2 * ρ - 1) * (ρ ^ 2 - 2 * ρ - 1) + 4 * ρ := by
        ring
      rw [hdecomp]
      positivity
    exact div_pos hnum_pos hden_sq_pos
  · intro y hy
    let a : ℝ := 1 + Real.sqrt 2
    let b : ℝ := y + 3
    have ha_gt_one : 1 < a := by
      dsimp [a]
      nlinarith [hsqrt_pos]
    have hab : a ≤ b := by
      dsimp [a, b]
      nlinarith [hy, hsqrt_lt_two]
    have hb_den_pos : 0 < b - 1 := by
      dsimp [b]
      nlinarith [hy]
    have hu_a : u a = 0 := by
      have hquad : a ^ 2 - 2 * a - 1 = 0 := by
        dsimp [a]
        nlinarith [hsqrt_sq]
      dsimp [u]
      rw [hquad, mul_zero, zero_div]
    have hy_lt_ub : y < u b := by
      have hbden : 0 < b - 1 := hb_den_pos
      have hmul :
          y * (b - 1) < b * (b ^ 2 - 2 * b - 1) := by
        dsimp [b]
        nlinarith [hy, sq_nonneg y, mul_nonneg hy.le (sq_nonneg y)]
      have hiff := (lt_div_iff₀ hbden).2 hmul
      simpa [u, mul_assoc] using hiff
    have hcont : ContinuousOn u (Set.Icc a b) := by
      unfold u
      refine ContinuousOn.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · intro x hx
        have hxgt : 1 < x := by nlinarith [ha_gt_one, hx.1]
        nlinarith
    have hy_mem : y ∈ Set.Ioo (u a) (u b) := by
      rw [hu_a]
      exact ⟨hy, hy_lt_ub⟩
    rcases intermediate_value_Ioo hab hcont hy_mem with ⟨ρ, hρmem, hρeq⟩
    exact ⟨ρ, hρmem.1, by simpa [u] using hρeq⟩

end Omega.Zeta
