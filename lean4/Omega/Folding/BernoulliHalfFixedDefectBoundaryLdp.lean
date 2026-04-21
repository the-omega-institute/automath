import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.BernoulliHalfFixedDefectFibonacciJordanFilter
import Omega.Folding.BernoulliHalfFixedDefectGrowth

namespace Omega.Folding

/-- The fixed-defect boundary probability is obtained by dividing the coefficient model by `2^m`.
-/
noncomputable def bernoulliHalfBoundaryProbability (m k : ℕ) : ℝ :=
  bernoulliHalfFixedDefectCoeff m k / (2 : ℝ) ^ m

/-- The fixed-defect boundary prefactor on the probability scale. -/
noncomputable def bernoulliHalfBoundaryLdpConstant (j : ℕ) : ℝ :=
  bernoulliHalfLeadingAmplitude * bernoulliHalfDelta3 ^ j / (Nat.factorial j : ℝ)

lemma bernoulliHalfDelta3_pos : 0 < bernoulliHalfDelta3 := by
  unfold bernoulliHalfDelta3
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith [Real.sqrt_nonneg 5]

lemma bernoulliHalfPhiHalf_pos : 0 < bernoulliHalfPhi / 2 := by
  have hphi : 0 < bernoulliHalfPhi := bernoulliHalfPhi_pos
  positivity

lemma bernoulliHalfBoundaryLdpConstant_pos (j : ℕ) : 0 < bernoulliHalfBoundaryLdpConstant j := by
  unfold bernoulliHalfBoundaryLdpConstant
  have hlead : 0 < bernoulliHalfLeadingAmplitude := bernoulliHalfLeadingAmplitude_pos
  have hdelta : 0 < bernoulliHalfDelta3 ^ j := pow_pos bernoulliHalfDelta3_pos _
  have hfact : 0 < (Nat.factorial j : ℝ) := by
    exact_mod_cast Nat.factorial_pos j
  positivity

/-- Paper label: `cor:fold-bernoulli-half-fixed-defect-boundary-ldp`. Dividing the fixed-defect
coefficient package by `2^m` yields the probability-scale bound
`(φ / 2)^m m^(⌊k / 3⌋)` together with the exact `3j` closed form and its logarithmic expansion. -/
theorem paper_fold_bernoulli_half_fixed_defect_boundary_ldp :
    (∀ k : ℕ, ∃ Ck > 0, ∀ m : ℕ,
      bernoulliHalfBoundaryProbability m k ≤
        Ck * (bernoulliHalfPhi / 2) ^ m * (m : ℝ) ^ (bernoulliHalfJordanOrder k - 1)) ∧
      (∀ m j : ℕ,
        bernoulliHalfBoundaryProbability m (3 * j) =
          bernoulliHalfBoundaryLdpConstant j * (bernoulliHalfPhi / 2) ^ m * (m : ℝ) ^ j) ∧
      (∀ j : ℕ, ∃ Bj : ℝ, ∀ m : ℕ, 1 ≤ m →
        Real.log (bernoulliHalfBoundaryProbability m (3 * j)) =
          (m : ℝ) * Real.log (bernoulliHalfPhi / 2) +
            (j : ℝ) * Real.log (m : ℝ) + Bj) := by
  rcases paper_fold_bernoulli_half_fixed_defect_growth with ⟨hbound, hprob3j, _hcoeff⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rcases hbound k with ⟨Ck, hCk_pos, hCk⟩
    refine ⟨Ck, hCk_pos, ?_⟩
    intro m
    have horder : bernoulliHalfJordanOrder k - 1 = k / 3 := by
      unfold bernoulliHalfJordanOrder
      omega
    have hpow2_pos : 0 < (2 : ℝ) ^ m := by positivity
    have hscaled :=
      div_le_div_of_nonneg_right (hCk m) (le_of_lt hpow2_pos)
    have hscaled' :
        bernoulliHalfBoundaryProbability m k ≤
          (Ck * bernoulliHalfPhi ^ m * (m : ℝ) ^ (k / 3)) / (2 : ℝ) ^ m := by
      simpa [bernoulliHalfBoundaryProbability] using hscaled
    refine hscaled'.trans_eq ?_
    rw [horder]
    rw [div_pow]
    field_simp [ne_of_gt hpow2_pos]
  · intro m j
    rw [bernoulliHalfBoundaryProbability, hprob3j, bernoulliHalfBoundaryLdpConstant, div_pow]
    field_simp
  · intro j
    refine ⟨Real.log (bernoulliHalfBoundaryLdpConstant j), ?_⟩
    intro m hm
    have hm_real_pos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hconst_pos : 0 < bernoulliHalfBoundaryLdpConstant j :=
      bernoulliHalfBoundaryLdpConstant_pos j
    have hphihalf_pos : 0 < (bernoulliHalfPhi / 2) ^ m :=
      pow_pos bernoulliHalfPhiHalf_pos _
    have hm_pow_pos : 0 < (m : ℝ) ^ j := by
      exact pow_pos hm_real_pos _
    rw [show bernoulliHalfBoundaryProbability m (3 * j) =
        bernoulliHalfBoundaryLdpConstant j * (bernoulliHalfPhi / 2) ^ m * (m : ℝ) ^ j by
          rw [bernoulliHalfBoundaryProbability, hprob3j, bernoulliHalfBoundaryLdpConstant, div_pow]
          field_simp]
    rw [mul_assoc, Real.log_mul hconst_pos.ne' (mul_ne_zero hphihalf_pos.ne' hm_pow_pos.ne'),
      Real.log_mul hphihalf_pos.ne' hm_pow_pos.ne', Real.log_pow, Real.log_pow]
    ring

end Omega.Folding
