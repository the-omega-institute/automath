import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

namespace Omega.Conclusion.ZeckendorfResetBoundedCLTAbsent

open Filter Topology

/-- Helper: `1 / √n → 0` as `n → ∞` (ℕ cast).
    cor:conclusion-zeckendorf-reset-no-central-limit -/
theorem one_div_sqrt_nat_tendsto_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / Real.sqrt n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp h1
  simpa using h2.inv_tendsto_atTop

/-- Helper: `1 / n → 0` as `n → ∞` (ℕ cast to ℝ).
    cor:conclusion-zeckendorf-reset-no-central-limit -/
theorem one_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop
  simpa using h1.inv_tendsto_atTop

/-- Bounded sequences over `√n` tend to zero.
    cor:conclusion-zeckendorf-reset-no-central-limit -/
theorem bounded_div_sqrt_tendsto_zero
    (f : ℕ → ℤ) (hbound : ∀ n, |f n| ≤ 1) :
    Tendsto (fun n => (f n : ℝ) / Real.sqrt n) atTop (𝓝 0) := by
  -- |(f n : ℝ) / √n| ≤ 1 / √n
  apply squeeze_zero_norm _ one_div_sqrt_nat_tendsto_zero
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  have habs : |((f n : ℝ))| ≤ 1 := by
    rw [show ((f n : ℝ)) = ((f n : ℤ) : ℝ) from rfl, ← Int.cast_abs]
    exact_mod_cast hbound n
  exact div_le_div_of_nonneg_right habs (Real.sqrt_nonneg _)

/-- Bounded sequences squared over `n` tend to zero.
    cor:conclusion-zeckendorf-reset-no-central-limit -/
theorem bounded_sq_div_tendsto_zero
    (f : ℕ → ℤ) (hbound : ∀ n, |f n| ≤ 1) :
    Tendsto (fun n => ((f n : ℝ))^2 / n) atTop (𝓝 0) := by
  apply squeeze_zero_norm _ one_div_nat_tendsto_zero
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by exact_mod_cast Nat.zero_le n : (0 : ℝ) ≤ n)]
  by_cases hn : (n : ℝ) = 0
  · rw [hn]; simp
  have hn_pos : (0 : ℝ) < n := lt_of_le_of_ne (by exact_mod_cast Nat.zero_le n) (Ne.symm hn)
  apply div_le_div_of_nonneg_right _ hn_pos.le
  have habs : |((f n : ℝ))| ≤ 1 := by
    rw [show ((f n : ℝ)) = ((f n : ℤ) : ℝ) from rfl, ← Int.cast_abs]
    exact_mod_cast hbound n
  have hsq : ((f n : ℝ))^2 ≤ 1 := by
    have h1 : ((f n : ℝ))^2 = |((f n : ℝ))|^2 := (sq_abs _).symm
    rw [h1]
    have h2 : |((f n : ℝ))|^2 ≤ 1^2 := by
      apply sq_le_sq'
      · linarith [abs_nonneg ((f n : ℝ))]
      · exact habs
    linarith [h2]
  calc |((f n : ℝ))^2| = ((f n : ℝ))^2 := abs_of_nonneg (sq_nonneg _)
    _ ≤ 1 := hsq

/-- Paper package: Zeckendorf reset fluctuations do not satisfy CLT scaling.
    cor:conclusion-zeckendorf-reset-no-central-limit -/
theorem paper_conclusion_zeckendorf_reset_no_central_limit
    (Nerr : ℕ → ℤ) (hbound : ∀ n, |Nerr n| ≤ 1) :
    Tendsto (fun n => (Nerr n : ℝ) / Real.sqrt n) atTop (𝓝 0) ∧
    Tendsto (fun n => ((Nerr n : ℝ))^2 / n) atTop (𝓝 0) :=
  ⟨bounded_div_sqrt_tendsto_zero Nerr hbound,
   bounded_sq_div_tendsto_zero Nerr hbound⟩

end Omega.Conclusion.ZeckendorfResetBoundedCLTAbsent
