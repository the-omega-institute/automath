import Mathlib

open scoped goldenRatio

namespace Omega.Conclusion

/-- The spectral-radius model for the truncated golden SPRT tail kernel. The factor
`exp (-(3/2) log φ)` is the concrete realization of `φ^(-3/2)`. -/
noncomputable def goldenSprtTailSpectralRadius (T : ℕ) : ℝ :=
  2 * Real.exp (-((3 / 2 : ℝ) * Real.log Real.goldenRatio)) *
    Real.cos (Real.pi / (2 * (T : ℝ)))

/-- Base-`2` tail exponent attached to the spectral radius. -/
noncomputable def goldenSprtTailExponent (T : ℕ) : ℝ :=
  -Real.log (goldenSprtTailSpectralRadius T) / Real.log 2

/-- The limiting golden Chernoff constant in natural-log coordinates. -/
noncomputable def goldenSprtChernoffConstant : ℝ :=
  ((3 / 2 : ℝ) * Real.log Real.goldenRatio - Real.log 2) / Real.log 2

/-- `π / (2T)` lies in the open right half of `(-π/2, π/2)` once `T ≥ 2`. -/
private lemma goldenSprt_angle_mem_Ioo (T : ℕ) (hT : 2 ≤ T) :
    Real.pi / (2 * (T : ℝ)) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hTgt1 : (1 : ℝ) < T := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hT
  have hden_pos : 0 < (2 : ℝ) * T := by positivity
  have hleft : -(Real.pi / 2) < Real.pi / (2 * (T : ℝ)) := by
    have hpos : 0 < Real.pi / (2 * (T : ℝ)) := by
      exact div_pos Real.pi_pos hden_pos
    have hneg : -(Real.pi / 2) < 0 := by
      nlinarith [Real.pi_pos]
    exact lt_trans hneg hpos
  have hden_lt : (2 : ℝ) < 2 * (T : ℝ) := by nlinarith
  have hinv_lt : 1 / (2 * (T : ℝ)) < 1 / (2 : ℝ) :=
    one_div_lt_one_div_of_lt (by positivity) hden_lt
  have hright : Real.pi / (2 * (T : ℝ)) < Real.pi / 2 := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_lt_mul_of_pos_left hinv_lt Real.pi_pos
  exact ⟨hleft, hright⟩

/-- Paper label: `thm:conclusion-golden-sprt-tail-exponent-chernoff-identity`.
For every truncation threshold `T ≥ 2`, the tail exponent is the golden Chernoff constant plus the
explicit cosine correction coming from the spectral radius formula. -/
theorem paper_conclusion_golden_sprt_tail_exponent_chernoff_identity (T : ℕ) (hT : 2 ≤ T) :
    goldenSprtTailExponent T =
      goldenSprtChernoffConstant - Real.log (Real.cos (Real.pi / (2 * (T : ℝ)))) / Real.log 2 := by
  have hlog2_ne : Real.log 2 ≠ 0 := by
    exact ne_of_gt (Real.log_pos one_lt_two)
  have hcos_pos : 0 < Real.cos (Real.pi / (2 * (T : ℝ))) := by
    exact Real.cos_pos_of_mem_Ioo (goldenSprt_angle_mem_Ioo T hT)
  have hexp_pos : 0 < Real.exp (-((3 / 2 : ℝ) * Real.log Real.goldenRatio)) := Real.exp_pos _
  have hmul_pos :
      0 < Real.exp (-((3 / 2 : ℝ) * Real.log Real.goldenRatio)) *
        Real.cos (Real.pi / (2 * (T : ℝ))) := by
    exact mul_pos hexp_pos hcos_pos
  unfold goldenSprtTailExponent goldenSprtChernoffConstant goldenSprtTailSpectralRadius
  rw [show 2 * Real.exp (-((3 / 2 : ℝ) * Real.log Real.goldenRatio)) *
      Real.cos (Real.pi / (2 * (T : ℝ))) =
        2 * (Real.exp (-((3 / 2 : ℝ) * Real.log Real.goldenRatio)) *
          Real.cos (Real.pi / (2 * (T : ℝ)))) by ring]
  rw [Real.log_mul (by norm_num) hmul_pos.ne', Real.log_mul hexp_pos.ne' hcos_pos.ne', Real.log_exp]
  have hmain :
      -(Real.log 2 + -(3 / 2 * Real.log Real.goldenRatio) +
          Real.log (Real.cos (Real.pi / (2 * (T : ℝ))))) /
        Real.log 2 =
        (3 / 2 * Real.log Real.goldenRatio - Real.log 2) / Real.log 2 -
          Real.log (Real.cos (Real.pi / (2 * (T : ℝ)))) / Real.log 2 := by
    field_simp [hlog2_ne]
    ring
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain

end Omega.Conclusion
