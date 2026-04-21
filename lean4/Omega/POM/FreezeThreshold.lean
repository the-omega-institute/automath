import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The golden ratio `φ = (1 + √5) / 2`. -/
def pomGoldenRatio : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- The affine lower bound coming from Jensen's inequality and the average fiber scale. -/
def pomJensenAffineLowerBound (q : ℝ) : ℝ :=
  Real.log pomGoldenRatio + q * (Real.log 2 - Real.log pomGoldenRatio)

/-- The affine lower bound coming from the maximal-fiber scale. -/
def pomMaxFiberAffineLowerBound (q : ℝ) : ℝ :=
  q * Real.log pomGoldenRatio / 2

/-- A doubled-denominator form of the freeze threshold:
`k_freeze = 2 log φ / (3 log φ - log 4)`. -/
def pomFreezeThreshold : ℝ :=
  (2 * Real.log pomGoldenRatio) / (3 * Real.log pomGoldenRatio - Real.log 4)

/-- Paper-facing package for the freeze-threshold computation. -/
def POMFreezeThresholdStatement : Prop :=
  (∀ q : ℝ,
      pomJensenAffineLowerBound q - pomMaxFiberAffineLowerBound q =
        Real.log pomGoldenRatio -
          q * (3 * Real.log pomGoldenRatio - Real.log 4) / 2) ∧
    pomJensenAffineLowerBound pomFreezeThreshold =
      pomMaxFiberAffineLowerBound pomFreezeThreshold ∧
    pomFreezeThreshold =
      Real.log pomGoldenRatio /
        (((3 : ℝ) / 2) * Real.log pomGoldenRatio - Real.log 2)

private lemma pomGoldenRatio_cube_gt_four : 4 < pomGoldenRatio ^ (3 : ℕ) := by
  have hsq : (Real.sqrt 5) ^ (2 : ℕ) = 5 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by positivity)]
  have hnonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold pomGoldenRatio
  nlinarith

private lemma pomLogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by positivity) (by positivity)]
  ring

private lemma pomAffineGap_formula (q : ℝ) :
    pomJensenAffineLowerBound q - pomMaxFiberAffineLowerBound q =
      Real.log pomGoldenRatio - q * (3 * Real.log pomGoldenRatio - Real.log 4) / 2 := by
  rw [pomLogFour]
  unfold pomJensenAffineLowerBound pomMaxFiberAffineLowerBound
  ring_nf

private lemma pomFreezeThreshold_denominator_pos :
    0 < 3 * Real.log pomGoldenRatio - Real.log 4 := by
  have hphi_pos : 0 < pomGoldenRatio := by
    unfold pomGoldenRatio
    positivity
  have hfrac_gt_one : 1 < pomGoldenRatio ^ (3 : ℕ) / 4 := by
    have hcube := pomGoldenRatio_cube_gt_four
    nlinarith
  calc
    0 < Real.log (pomGoldenRatio ^ (3 : ℕ) / 4) := Real.log_pos hfrac_gt_one
    _ = Real.log (pomGoldenRatio ^ (3 : ℕ)) - Real.log 4 := by
      rw [Real.log_div (by positivity) (by positivity)]
    _ = 3 * Real.log pomGoldenRatio - Real.log 4 := by
      rw [show pomGoldenRatio ^ (3 : ℕ) = pomGoldenRatio * pomGoldenRatio * pomGoldenRatio by
        ring]
      rw [Real.log_mul (by positivity) (by positivity)]
      rw [Real.log_mul (by positivity) hphi_pos.ne']
      ring_nf

/-- Paper label: `prop:pom-freeze-threshold`.
The Jensen/average-scale and maximal-fiber affine lower bounds cross at the stated `k_freeze`. -/
theorem paper_pom_freeze_threshold : POMFreezeThresholdStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact pomAffineGap_formula q
  · have hden :
        3 * Real.log pomGoldenRatio - Real.log 4 ≠ 0 :=
      ne_of_gt pomFreezeThreshold_denominator_pos
    have hdiff := pomAffineGap_formula pomFreezeThreshold
    have hmul :
        pomFreezeThreshold * (3 * Real.log pomGoldenRatio - Real.log 4) =
          2 * Real.log pomGoldenRatio := by
      unfold pomFreezeThreshold
      rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hden, mul_one]
    have hzero :
        Real.log pomGoldenRatio -
            pomFreezeThreshold * (3 * Real.log pomGoldenRatio - Real.log 4) / 2 = 0 := by
      rw [hmul]
      ring
    linarith
  · have hden :
        3 * Real.log pomGoldenRatio - Real.log 4 ≠ 0 :=
      ne_of_gt pomFreezeThreshold_denominator_pos
    unfold pomFreezeThreshold
    rw [pomLogFour]
    field_simp [hden]

end

end Omega.POM
