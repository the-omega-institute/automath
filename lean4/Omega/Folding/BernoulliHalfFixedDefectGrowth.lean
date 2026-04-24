import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.BernoulliHalfLowTempCubicActivation

namespace Omega.Folding

/-- The Perron value at `u = 0` for the Bernoulli-half branch. -/
noncomputable def bernoulliHalfPhi : ℝ :=
  ((1 : ℝ) + Real.sqrt 5) / 2

/-- The constant `C(0) = φ² / √5 = (5 + 3√5) / 10` from the dominant-root decomposition. -/
noncomputable def bernoulliHalfLeadingAmplitude : ℝ :=
  (5 + 3 * Real.sqrt 5) / 10

/-- The normalized cubic activation coefficient `δ₃ = c₃ / φ`. -/
noncomputable def bernoulliHalfDelta3 : ℝ :=
  (3 * Real.sqrt 5 - 5) / 10

/-- The explicit `3j`-mode main term extracted from the cubic activation law. -/
noncomputable def bernoulliHalfFixedDefectCoeff (m k : ℕ) : ℝ :=
  if k % 3 = 0 then
    bernoulliHalfLeadingAmplitude * bernoulliHalfPhi ^ m *
      bernoulliHalfDelta3 ^ (k / 3) * (m : ℝ) ^ (k / 3) / (Nat.factorial (k / 3) : ℝ)
  else
    0

/-- A concrete growth constant bounding the fixed-defect coefficient model by
`φ^m m^(⌊k / 3⌋)`. -/
noncomputable def bernoulliHalfGrowthConstant (k : ℕ) : ℝ :=
  bernoulliHalfLeadingAmplitude *
    ((bernoulliHalfDelta3 ^ (k / 3) / (Nat.factorial (k / 3) : ℝ)) ^ 2 + 1)

lemma bernoulliHalfPhi_pos : 0 < bernoulliHalfPhi := by
  unfold bernoulliHalfPhi
  have hsqrt : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

lemma bernoulliHalfLeadingAmplitude_pos : 0 < bernoulliHalfLeadingAmplitude := by
  unfold bernoulliHalfLeadingAmplitude
  have hsqrt : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

lemma bernoulliHalfGrowthConstant_pos (k : ℕ) : 0 < bernoulliHalfGrowthConstant k := by
  unfold bernoulliHalfGrowthConstant
  have hlead : 0 < bernoulliHalfLeadingAmplitude := bernoulliHalfLeadingAmplitude_pos
  have hsquare : 0 ≤
      (bernoulliHalfDelta3 ^ (k / 3) / (Nat.factorial (k / 3) : ℝ)) ^ 2 := sq_nonneg _
  nlinarith

/-- Paper label: `cor:fold-bernoulli-half-fixed-defect-growth`. -/
theorem paper_fold_bernoulli_half_fixed_defect_growth :
    (∀ k : ℕ, ∃ Ck > 0, ∀ m : ℕ,
      bernoulliHalfFixedDefectCoeff m k ≤ Ck * bernoulliHalfPhi ^ m * (m : ℝ) ^ (k / 3)) ∧
      (∀ m j : ℕ,
        bernoulliHalfFixedDefectCoeff m (3 * j) =
          bernoulliHalfLeadingAmplitude * bernoulliHalfPhi ^ m *
            bernoulliHalfDelta3 ^ j * (m : ℝ) ^ j / (Nat.factorial j : ℝ)) ∧
      perronTaylorCoeff bernoulliHalfPerronRoot 3 = bernoulliHalfPhi * bernoulliHalfDelta3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    refine ⟨bernoulliHalfGrowthConstant k, bernoulliHalfGrowthConstant_pos k, ?_⟩
    intro m
    by_cases hdiv : k % 3 = 0
    · set A : ℝ := bernoulliHalfLeadingAmplitude * bernoulliHalfPhi ^ m * (m : ℝ) ^ (k / 3)
      set x : ℝ := bernoulliHalfDelta3 ^ (k / 3) / (Nat.factorial (k / 3) : ℝ)
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        have hlead : 0 ≤ bernoulliHalfLeadingAmplitude := le_of_lt bernoulliHalfLeadingAmplitude_pos
        have hphi : 0 ≤ bernoulliHalfPhi ^ m := by
          exact pow_nonneg (le_of_lt bernoulliHalfPhi_pos) m
        have hm : 0 ≤ (m : ℝ) ^ (k / 3) := by positivity
        exact mul_nonneg (mul_nonneg hlead hphi) hm
      have hx : x ≤ x ^ 2 + 1 := by
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hx hA_nonneg
      have hleft :
          A * x =
            bernoulliHalfLeadingAmplitude * bernoulliHalfPhi ^ m * bernoulliHalfDelta3 ^ (k / 3) *
              (m : ℝ) ^ (k / 3) / (Nat.factorial (k / 3) : ℝ) := by
        dsimp [A, x]
        ring
      have hright :
          A * (x ^ 2 + 1) =
            bernoulliHalfGrowthConstant k * bernoulliHalfPhi ^ m * (m : ℝ) ^ (k / 3) := by
        unfold bernoulliHalfGrowthConstant
        dsimp [A, x]
        ring
      simp [bernoulliHalfFixedDefectCoeff, hdiv]
      calc
        bernoulliHalfLeadingAmplitude * bernoulliHalfPhi ^ m * bernoulliHalfDelta3 ^ (k / 3) *
            (m : ℝ) ^ (k / 3) / (Nat.factorial (k / 3) : ℝ)
            = A * x := by symm; exact hleft
        _ ≤ A * (x ^ 2 + 1) := hmul
        _ = bernoulliHalfGrowthConstant k * bernoulliHalfPhi ^ m * (m : ℝ) ^ (k / 3) := hright
    · have hnonneg :
          0 ≤ bernoulliHalfGrowthConstant k * bernoulliHalfPhi ^ m * (m : ℝ) ^ (k / 3) := by
        have hC : 0 ≤ bernoulliHalfGrowthConstant k := le_of_lt (bernoulliHalfGrowthConstant_pos k)
        have hphi : 0 ≤ bernoulliHalfPhi ^ m := by
          exact pow_nonneg (le_of_lt bernoulliHalfPhi_pos) m
        have hm : 0 ≤ (m : ℝ) ^ (k / 3) := by positivity
        exact mul_nonneg (mul_nonneg hC hphi) hm
      simpa [bernoulliHalfFixedDefectCoeff, hdiv] using hnonneg
  · intro m j
    have hdiv : (3 * j) % 3 = 0 := by omega
    simp [bernoulliHalfFixedDefectCoeff, hdiv]
  · have hcoeff := paper_fold_bernoulli_half_low_temp_cubic_activation.2.2
    calc
      perronTaylorCoeff bernoulliHalfPerronRoot 3 = (1 : ℝ) / 2 - Real.sqrt 5 / 10 := by
        simpa using hcoeff
      _ = bernoulliHalfPhi * bernoulliHalfDelta3 := by
        unfold bernoulliHalfPhi bernoulliHalfDelta3
        have hsqrt : (Real.sqrt 5) ^ 2 = 5 := by
          rw [Real.sq_sqrt]
          positivity
        nlinarith

end Omega.Folding
