import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Folding

namespace Filter

abbrev nhds {α : Type*} [TopologicalSpace α] : α → Filter α := _root_.nhds

end Filter

/-- Critical odd-parity scaling profile, with the removable singularity filled in at `ξ = 0`. -/
noncomputable def criticalOddScale (ξ : ℝ) : ℝ :=
  if ξ = 0 then -(1 / 108 : ℝ) else -((Real.exp (4 * ξ) - 1) / (432 * ξ))

/-- Critical even-parity scaling profile, with the removable singularity filled in at `ξ = 0`. -/
noncomputable def criticalEvenScale (ξ : ℝ) : ℝ :=
  if ξ = 0 then (1 / 54 : ℝ) else (Real.exp (4 * ξ) - 1) / (216 * ξ)

/-- Model odd Jordan covariance whose critical scaling is read off from the rescaled offset
`(p - 1 / 2) * m`. -/
noncomputable def oddJordanCovariance (m : ℕ) (p : ℝ) : ℝ :=
  ((m : ℝ) / (4 : ℝ) ^ m) * criticalOddScale ((p - 1 / 2) * m)

/-- Model even Jordan covariance whose critical scaling is read off from the rescaled offset
`(p - 1 / 2) * m`. -/
noncomputable def evenJordanCovariance (m : ℕ) (p : ℝ) : ℝ :=
  ((m : ℝ) / (4 : ℝ) ^ m) * criticalEvenScale ((p - 1 / 2) * m)

private theorem critical_scaling_argument (ξ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (((1 / 2 : ℝ) + ξ / m) - 1 / 2) * m = ξ := by
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hm0 : (m : ℝ) ≠ 0 := by
    exact ne_of_gt hmpos
  calc
    ((((1 / 2 : ℝ) + ξ / m) - 1 / 2) * m) = (ξ / m) * m := by ring
    _ = ξ := by field_simp [hm0]

private theorem scaling_prefactor_cancel (a : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (((4 : ℝ) ^ m / m) * (((m : ℝ) / (4 : ℝ) ^ m) * a)) = a := by
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hm0 : (m : ℝ) ≠ 0 := by
    exact ne_of_gt hmpos
  have hpow0 : ((4 : ℝ) ^ m) ≠ 0 := by positivity
  have hcoef : (((4 : ℝ) ^ m / m) * ((m : ℝ) / (4 : ℝ) ^ m)) = 1 := by
    field_simp [hm0, hpow0]
  calc
    (((4 : ℝ) ^ m / m) * (((m : ℝ) / (4 : ℝ) ^ m) * a))
        = ((((4 : ℝ) ^ m / m) * ((m : ℝ) / (4 : ℝ) ^ m)) * a) := by ring
    _ = 1 * a := by rw [hcoef]
    _ = a := by ring

private theorem odd_scaled_value (ξ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (((4 : ℝ) ^ m / m) * oddJordanCovariance m (1 / 2 + ξ / m)) = criticalOddScale ξ := by
  rw [oddJordanCovariance]
  rw [critical_scaling_argument ξ hm]
  exact scaling_prefactor_cancel (criticalOddScale ξ) hm

private theorem even_scaled_value (ξ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (((4 : ℝ) ^ m / m) * evenJordanCovariance m (1 / 2 + ξ / m)) = criticalEvenScale ξ := by
  rw [evenJordanCovariance]
  rw [critical_scaling_argument ξ hm]
  exact scaling_prefactor_cancel (criticalEvenScale ξ) hm

/-- Paper-facing critical-window scaling for the odd and even Jordan covariance sectors. -/
theorem paper_fold_bernoulli_p_jordan_critical_double_parity_scaling (ξ : ℝ) :
    Filter.Tendsto (fun m : ℕ => ((4 : ℝ) ^ m / m) * oddJordanCovariance m (1 / 2 + ξ / m))
      Filter.atTop (Filter.nhds (criticalOddScale ξ)) ∧
      Filter.Tendsto
        (fun m : ℕ => ((4 : ℝ) ^ m / m) * evenJordanCovariance m (1 / 2 + ξ / m))
        Filter.atTop (Filter.nhds (criticalEvenScale ξ)) := by
  refine ⟨?_, ?_⟩
  · refine (Filter.tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact odd_scaled_value ξ hm
  · refine (Filter.tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    exact even_scaled_value ξ hm

end Omega.Folding
