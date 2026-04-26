import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

private theorem xi_time_part70_binfold_uniform_empirical_two_point_law_ratio_tendsto_inv_golden :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 1)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  rw [Real.inv_goldenRatio]
  simpa using tendsto_fib_div_fib_succ_atTop

private theorem xi_time_part70_binfold_uniform_empirical_two_point_law_ratio_tendsto_inv_golden_shift :
    Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  have h := tendsto_fib_div_fib_succ_atTop.comp (tendsto_add_atTop_nat (1 : ℕ))
  rw [Real.inv_goldenRatio]
  simpa [Nat.add_assoc] using h

private theorem xi_time_part70_binfold_uniform_empirical_two_point_law_ratio_tendsto_inv_golden_sq :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 2)) atTop
      (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 2)) := by
  have hprod :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) *
            ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)))
        atTop (nhds ((Real.goldenRatio⁻¹ : ℝ) * Real.goldenRatio⁻¹)) := by
    exact
      xi_time_part70_binfold_uniform_empirical_two_point_law_ratio_tendsto_inv_golden.mul
        xi_time_part70_binfold_uniform_empirical_two_point_law_ratio_tendsto_inv_golden_shift
  have hprod' :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) *
            ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)))
        atTop (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 2)) := by
    simpa [pow_two] using hprod
  refine Tendsto.congr' ?_ hprod'
  filter_upwards [Filter.Eventually.of_forall fun _ => True.intro] with n _
  have hfib : (Nat.fib (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos n)))
  field_simp [hfib]

/-- Paper label: `thm:xi-time-part70-binfold-uniform-empirical-two-point-law`. -/
theorem paper_xi_time_part70_binfold_uniform_empirical_two_point_law
    (avg : ℕ → (ℝ → ℝ) → ℝ)
    (havg : ∀ (m : ℕ) (f : ℝ → ℝ),
      avg m f =
        (Nat.fib (m + 1) : ℝ) / Nat.fib (m + 2) * f 1 +
          (Nat.fib m : ℝ) / Nat.fib (m + 2) * f (Real.goldenRatio⁻¹)) :
    ∀ f : ℝ → ℝ,
      Tendsto (fun m : ℕ => avg m f) atTop
        (nhds
          ((Real.goldenRatio⁻¹ : ℝ) * f 1 +
            (Real.goldenRatio⁻¹ : ℝ) ^ 2 * f (Real.goldenRatio⁻¹))) := by
  intro f
  have hlimit :
      Tendsto
        (fun m : ℕ =>
          (Nat.fib (m + 1) : ℝ) / Nat.fib (m + 2) * f 1 +
            (Nat.fib m : ℝ) / Nat.fib (m + 2) * f (Real.goldenRatio⁻¹))
        atTop
        (nhds
          ((Real.goldenRatio⁻¹ : ℝ) * f 1 +
            (Real.goldenRatio⁻¹ : ℝ) ^ 2 * f (Real.goldenRatio⁻¹))) := by
    exact
      (xi_time_part70_binfold_uniform_empirical_two_point_law_ratio_tendsto_inv_golden_shift.mul
        tendsto_const_nhds).add
        (xi_time_part70_binfold_uniform_empirical_two_point_law_ratio_tendsto_inv_golden_sq.mul
          tendsto_const_nhds)
  refine Tendsto.congr' ?_ hlimit
  filter_upwards [Filter.Eventually.of_forall fun _ => True.intro] with m _
  exact (havg m f).symm

end Omega.Zeta
