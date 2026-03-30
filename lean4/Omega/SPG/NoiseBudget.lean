import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.SPG

/-- Rearranged noise-budget threshold from the operator-norm lower bound.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem noiseBudget_threshold
    {n m : ℕ} {ε δ : ℝ}
    (hn : 0 < n) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hbound : ((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ)) * ε ≤ δ) :
    ε ≤ Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
  have hsqrt_pos : 0 < Real.sqrt (2 * n : ℝ) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hpow_pos : 0 < (2 : ℝ) ^ (m / 2 : ℝ) := by
    exact Real.rpow_pos_of_pos (by positivity) _
  have hfac_pos : 0 < (1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ) := by
    positivity
  have hfac_ne : (1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ) ≠ 0 := ne_of_gt hfac_pos
  have hdiv : ε ≤ δ / (((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ))) := by
    exact (le_div_iff₀ hfac_pos).mpr hbound
  have hrewrite :
      δ / (((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ))) =
        Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
    field_simp [hfac_ne, hsqrt_pos.ne', hpow_pos.ne']
    ring_nf
    rw [← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2)]
    ring
  rw [hrewrite]
  exact hdiv

/-- Equivalent threshold form for the dyadic holographic noise budget.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem noiseBudget_threshold_iff
    {n m : ℕ} {ε δ : ℝ} (hn : 0 < n) :
    (((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ)) * ε ≤ δ)
      ↔ ε ≤ Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
  constructor
  · intro h
    exact noiseBudget_threshold hn (by positivity) (by positivity) h
  · intro h
    have hsqrt_pos : 0 < Real.sqrt (2 * n : ℝ) := by
      apply Real.sqrt_pos.mpr
      positivity
    have hpow_pos : 0 < (2 : ℝ) ^ (m / 2 : ℝ) := by
      exact Real.rpow_pos_of_pos (by positivity) _
    have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ))
    have hrewrite :
        ((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ)) *
            (Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ))) = δ := by
      field_simp [hsqrt_pos.ne', hpow_pos.ne']
      ring_nf
      rw [← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2)]
      ring
    simpa [mul_assoc, hrewrite] using hmul

end Omega.SPG
