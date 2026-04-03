import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.SPG

/-- Rearranged noise-budget threshold from the operator-norm lower bound.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem noiseBudget_threshold
    {n m : ℕ} {ε δ : ℝ}
    (hn : 0 < n) (_hε : 0 ≤ ε) (_hδ : 0 ≤ δ)
    (hbound : ((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ)) * ε ≤ δ) :
    ε ≤ Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
  have hsqrt_pos : 0 < Real.sqrt (2 * n : ℝ) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hpow_pos : 0 < (2 : ℝ) ^ (m / 2 : ℝ) := by
    exact Real.rpow_pos_of_pos (by positivity) _
  have hfac_pos : 0 < (1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ) := by
    positivity
  have hdiv : ε ≤ δ / (((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ))) := by
    exact (le_div_iff₀ hfac_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbound)
  have hpow_inv : (2 : ℝ) ^ (-(m / 2 : ℝ)) = ((2 : ℝ) ^ (m / 2 : ℝ))⁻¹ := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2)]
  have hrewrite :
      δ / (((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ))) =
        Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
    rw [hpow_inv]
    field_simp [hsqrt_pos.ne', hpow_pos.ne']
  rw [hrewrite] at hdiv
  exact hdiv

/-- Equivalent threshold form for the dyadic holographic noise budget.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem noiseBudget_threshold_iff
    {n m : ℕ} {ε δ : ℝ} (hn : 0 < n) :
    (((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ)) * ε ≤ δ)
      ↔ ε ≤ Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
  have hsqrt_pos : 0 < Real.sqrt (2 * n : ℝ) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hpow_pos : 0 < (2 : ℝ) ^ (m / 2 : ℝ) := by
    exact Real.rpow_pos_of_pos (by positivity) _
  have hfac_pos : 0 < (1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ) := by
    positivity
  have hpow_inv : (2 : ℝ) ^ (-(m / 2 : ℝ)) = ((2 : ℝ) ^ (m / 2 : ℝ))⁻¹ := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2)]
  have hrewrite :
      δ / (((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ))) =
        Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
    rw [hpow_inv]
    field_simp [hsqrt_pos.ne', hpow_pos.ne']
  calc
    (((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ)) * ε ≤ δ)
        ↔ ε ≤ δ / (((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ))) := by
          constructor
          · intro h
            exact (le_div_iff₀ hfac_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h)
          · intro h
            have h' : ε * ((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ)) ≤ δ :=
              (le_div_iff₀ hfac_pos).1 h
            simpa [mul_comm, mul_left_comm, mul_assoc] using h'
    _ ↔ ε ≤ Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
          rw [hrewrite]

/-- Noise-budget threshold decreases with the dyadic resolution parameter.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem noiseBudget_threshold_antitone_in_m
    {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 ≤ δ)
    {m m' : ℕ} (hmm' : m ≤ m') :
    Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m' / 2 : ℝ))
      ≤ Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
  have hfac_nonneg : 0 ≤ Real.sqrt (2 * n : ℝ) * δ := by
    positivity
  have hhalf : (m : ℝ) / 2 ≤ (m' : ℝ) / 2 := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmm') (by norm_num : (0 : ℝ) ≤ 2)
  have hexp : -(m' / 2 : ℝ) ≤ -(m / 2 : ℝ) := by
    exact neg_le_neg hhalf
  have hpow : (2 : ℝ) ^ (-(m' / 2 : ℝ)) ≤ (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  exact mul_le_mul_of_nonneg_left hpow hfac_nonneg

/-- Noise-budget threshold is strictly decreasing in the dyadic resolution parameter.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem noiseBudget_threshold_strict_antitone_in_m
    {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ)
    {m m' : ℕ} (hmm' : m < m') :
    Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m' / 2 : ℝ)) <
      Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
  have hhalf : (m : ℝ) / 2 < (m' : ℝ) / 2 := by
    have hcast : (m : ℝ) < (m' : ℝ) := by exact_mod_cast hmm'
    linarith
  have hexp : -(m' / 2 : ℝ) < -(m / 2 : ℝ) := by
    exact neg_lt_neg hhalf
  have hpow : (2 : ℝ) ^ (-(m' / 2 : ℝ)) < (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hexp
  have hfac_pos : 0 < Real.sqrt (2 * n : ℝ) * δ := by
    have hsqrt_pos : 0 < Real.sqrt (2 * n : ℝ) := by
      apply Real.sqrt_pos.mpr
      positivity
    exact mul_pos hsqrt_pos hδ
  exact mul_lt_mul_of_pos_left hpow hfac_pos

/-- The dyadic noise-budget threshold is injective in the resolution parameter.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem noiseBudget_threshold_eq_iff
    {n : ℕ} {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ)
    {m m' : ℕ} :
    Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) =
      Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m' / 2 : ℝ)) ↔ m = m' := by
  constructor
  · intro hEq
    by_cases hmm' : m = m'
    · exact hmm'
    · have hlt_or_gt : m < m' ∨ m' < m := lt_or_gt_of_ne hmm'
      rcases hlt_or_gt with hlt | hgt
      · have hlt' := noiseBudget_threshold_strict_antitone_in_m hn hδ hlt
        rw [hEq] at hlt'
        exact (lt_irrefl _ hlt').elim
      · have hgt' := noiseBudget_threshold_strict_antitone_in_m hn hδ hgt
        rw [hEq] at hgt'
        exact (lt_irrefl _ hgt').elim
  · intro h
    rw [h]

/-- Paper-facing wrapper for the dyadic noise-budget threshold equivalence.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem paper_noiseBudget_threshold_iff
    {n m : ℕ} {ε δ : ℝ} (hn : 0 < n) :
    (((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ)) * ε ≤ δ)
      ↔ ε ≤ Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
  simpa using noiseBudget_threshold_iff (n := n) (m := m) (ε := ε) (δ := δ) hn

end Omega.SPG
