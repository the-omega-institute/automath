import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

namespace Omega.Conclusion.CycleRankSaturation

open Filter Topology

/-- The natural exponential scale for boundary cycle rank growth. -/
def cycleRankScale (n : ℕ) : ℝ :=
  (n : ℝ) * (2 : ℝ) ^ (n - 1)

/-- A minimal seed for the extracted quantitative content of `liminf aₙ > 0`. -/
def PositiveLiminf (a : ℕ → ℝ) : Prop :=
  ∃ δ > 0, ∀ᶠ n in atTop, δ ≤ a n

lemma cycleRankScale_nonneg (n : ℕ) : 0 ≤ cycleRankScale n := by
  dsimp [cycleRankScale]
  positivity

/-- If the area density stays eventually positive while `Xₙ / 2ⁿ → 0`, then the cycle rank grows
    on the `Θ(n 2^{n-1})` scale.
    cor:conclusion-boundary-cycle-rank-density-explosion -/
theorem paper_conclusion_boundary_cycle_rank_density_explosion
    (r A X c a : ℕ → ℝ)
    (hA : ∀ n, A n = cycleRankScale n * a n)
    (hrank : ∀ n, r n = A n - X n + c n)
    (hc_one : ∀ n, 1 ≤ c n)
    (hr_nonneg : ∀ n, 0 ≤ r n)
    (hr_le_A : ∀ n, r n ≤ A n)
    (hA_le : ∀ n, A n ≤ cycleRankScale n)
    (hX_nonneg : ∀ n, 0 ≤ X n)
    (ha : PositiveLiminf a)
    (hX_small : Tendsto (fun n => X n / (2 : ℝ) ^ n) atTop (𝓝 0)) :
    (∃ C₁ > 0, ∀ᶠ n in atTop, C₁ * cycleRankScale n ≤ r n) ∧
      (∃ C₂ > 0, ∀ᶠ n in atTop, r n ≤ C₂ * cycleRankScale n) ∧
      ((fun n => r n) =Θ[atTop] fun n => cycleRankScale n) := by
  rcases ha with ⟨δ, hδpos, hδevent⟩
  have hXevent : ∀ᶠ n in atTop, |X n / (2 : ℝ) ^ n| < δ / 4 := by
    have hnhds : {x : ℝ | |x| < δ / 4} ∈ 𝓝 (0 : ℝ) := by
      simpa [Metric.ball, Real.dist_eq] using Metric.ball_mem_nhds (0 : ℝ) (by positivity)
    exact hX_small hnhds
  have hge1 : ∀ᶠ n in atTop, 1 ≤ n := Filter.eventually_ge_atTop 1
  have hLowerEvent : ∀ᶠ n in atTop, (δ / 2) * cycleRankScale n ≤ r n := by
    filter_upwards [hδevent, hXevent, hge1] with n hδn hXn hn
    have hA_lower : δ * cycleRankScale n ≤ A n := by
      rw [hA n]
      have hscale_nonneg : 0 ≤ cycleRankScale n := cycleRankScale_nonneg n
      nlinarith
    have hpow_pos : 0 < (2 : ℝ) ^ n := by positivity
    have hX_upper' : X n < (δ / 4) * (2 : ℝ) ^ n := by
      have hdiv := (abs_lt.mp hXn).2
      exact (div_lt_iff₀ hpow_pos).mp hdiv
    have hX_upper : X n ≤ (δ / 2) * cycleRankScale n := by
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨k, rfl⟩
      have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      have hscale :
          (δ / 4) * (2 : ℝ) ^ (k + 1) ≤ (δ / 2) * cycleRankScale (k + 1) := by
        calc
          (δ / 4) * (2 : ℝ) ^ (k + 1) = (δ / 2) * (2 : ℝ) ^ k := by
            rw [pow_succ]
            ring
          _ ≤ (δ / 2) * (((k : ℝ) + 1) * (2 : ℝ) ^ k) := by
            have hbase :
                (δ / 2) * (2 : ℝ) ^ k * 1 ≤ (δ / 2) * (2 : ℝ) ^ k * ((k : ℝ) + 1) := by
              gcongr
            simpa [mul_assoc, mul_left_comm, mul_comm] using hbase
          _ = (δ / 2) * cycleRankScale (k + 1) := by
            simp [cycleRankScale, mul_assoc, mul_left_comm, mul_comm]
      exact le_trans (le_of_lt hX_upper') hscale
    rw [hrank n]
    nlinarith [hA_lower, hX_upper, hc_one n]
  have hUpperEvent : ∀ᶠ n in atTop, r n ≤ 1 * cycleRankScale n := by
    exact Filter.Eventually.of_forall fun n => by
      nlinarith [hr_le_A n, hA_le n]
  have hLower : ∃ C₁ > 0, ∀ᶠ n in atTop, C₁ * cycleRankScale n ≤ r n := by
    exact ⟨δ / 2, by positivity, hLowerEvent⟩
  have hUpper : ∃ C₂ > 0, ∀ᶠ n in atTop, r n ≤ C₂ * cycleRankScale n := by
    exact ⟨1, by norm_num, hUpperEvent⟩
  have hBigO₁ : (fun n => r n) =O[atTop] fun n => cycleRankScale n := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hUpperEvent] with n hn
    rw [Real.norm_of_nonneg (hr_nonneg n), Real.norm_of_nonneg (cycleRankScale_nonneg n)]
    simpa using hn
  have hBigO₂ : (fun n => cycleRankScale n) =O[atTop] fun n => r n := by
    refine Asymptotics.IsBigO.of_bound (2 / δ) ?_
    filter_upwards [hLowerEvent] with n hn
    rw [Real.norm_of_nonneg (cycleRankScale_nonneg n), Real.norm_of_nonneg (hr_nonneg n)]
    have hδ' : 0 < δ := hδpos
    have hcoef : 0 < δ / 2 := by positivity
    have hdiv : cycleRankScale n ≤ r n / (δ / 2) := by
      rw [le_div_iff₀ hcoef]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hn
    have hδne : δ ≠ 0 := ne_of_gt hδ'
    calc
      cycleRankScale n ≤ r n / (δ / 2) := hdiv
      _ = (2 / δ) * r n := by
        field_simp [hδne]
  exact ⟨hLower, hUpper, ⟨hBigO₁, hBigO₂⟩⟩

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
