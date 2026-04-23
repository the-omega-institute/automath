import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The dominant contribution: every top-real-part pole contributes with the same amplified base
`B^(kn)`. -/
def abel_power_base_gap_amplification_dominant_contribution
    {M : ℕ} (dominantBase : ℝ) (k n : ℕ) (dominantCoeff : Fin M → ℝ) : ℝ :=
  ∑ j : Fin M, dominantCoeff j * dominantBase ^ (k * n)

/-- The subleading contribution is compressed by the additional gap factor `η^(kn)`. -/
def abel_power_base_gap_amplification_subleading_contribution
    {L : ℕ} (dominantBase gapRatio : ℝ) (k n : ℕ) (subleadingCoeff : Fin L → ℝ) : ℝ :=
  ∑ j : Fin L, subleadingCoeff j * (dominantBase * gapRatio) ^ (k * n)

/-- The total coefficient is the sum of the dominant cluster and the subleading remainder. -/
def abel_power_base_gap_amplification_coefficient
    {M L : ℕ} (dominantBase gapRatio : ℝ) (k n : ℕ) (dominantCoeff : Fin M → ℝ)
    (subleadingCoeff : Fin L → ℝ) : ℝ :=
  abel_power_base_gap_amplification_dominant_contribution dominantBase k n dominantCoeff +
    abel_power_base_gap_amplification_subleading_contribution
      dominantBase gapRatio k n subleadingCoeff

/-- Paper label: `thm:abel-power-base-gap-amplification`. Splitting the geometric contribution into
the top-real-part cluster and the subleading cluster isolates an error term smaller by the
amplified factor `η^(kn)`. -/
theorem paper_abel_power_base_gap_amplification
    {M L : ℕ} (dominantBase gapRatio : ℝ) (k n : ℕ) (dominantCoeff : Fin M → ℝ)
    (subleadingCoeff : Fin L → ℝ) (hBase : 0 ≤ dominantBase) (hGap : 0 ≤ gapRatio) :
    abel_power_base_gap_amplification_coefficient
        dominantBase gapRatio k n dominantCoeff subleadingCoeff =
      dominantBase ^ (k * n) * ∑ j : Fin M, dominantCoeff j +
        dominantBase ^ (k * n) * gapRatio ^ (k * n) * ∑ j : Fin L, subleadingCoeff j ∧
      |abel_power_base_gap_amplification_coefficient
          dominantBase gapRatio k n dominantCoeff subleadingCoeff -
        abel_power_base_gap_amplification_dominant_contribution
          dominantBase k n dominantCoeff| ≤
        dominantBase ^ (k * n) * gapRatio ^ (k * n) * ∑ j : Fin L, |subleadingCoeff j| := by
  let m := k * n
  have hmulpow : (dominantBase * gapRatio) ^ m = dominantBase ^ m * gapRatio ^ m := by
    rw [mul_pow]
  have hdom :
      abel_power_base_gap_amplification_dominant_contribution dominantBase k n dominantCoeff =
        dominantBase ^ m * ∑ j : Fin M, dominantCoeff j := by
    simpa [abel_power_base_gap_amplification_dominant_contribution, m, mul_comm, mul_left_comm,
      mul_assoc] using
      (Finset.sum_mul (s := Finset.univ) (f := fun j : Fin M => dominantCoeff j)
        (a := dominantBase ^ m)).symm
  have hsub :
      abel_power_base_gap_amplification_subleading_contribution
          dominantBase gapRatio k n subleadingCoeff =
        dominantBase ^ m * gapRatio ^ m * ∑ j : Fin L, subleadingCoeff j := by
    rw [abel_power_base_gap_amplification_subleading_contribution, hmulpow]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Finset.sum_mul (s := Finset.univ) (f := fun j : Fin L => subleadingCoeff j)
        (a := dominantBase ^ m * gapRatio ^ m)).symm
  have hsplit :
      abel_power_base_gap_amplification_coefficient
          dominantBase gapRatio k n dominantCoeff subleadingCoeff -
        abel_power_base_gap_amplification_dominant_contribution dominantBase k n dominantCoeff =
      abel_power_base_gap_amplification_subleading_contribution
        dominantBase gapRatio k n subleadingCoeff := by
    simp [abel_power_base_gap_amplification_coefficient]
  refine ⟨?_, ?_⟩
  · rw [abel_power_base_gap_amplification_coefficient, hdom, hsub]
  · rw [hsplit]
    calc
      |abel_power_base_gap_amplification_subleading_contribution
          dominantBase gapRatio k n subleadingCoeff|
        = |∑ j : Fin L, subleadingCoeff j * (dominantBase * gapRatio) ^ m| := by
            rfl
      _ ≤ ∑ j : Fin L, |subleadingCoeff j * (dominantBase * gapRatio) ^ m| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin L, |subleadingCoeff j| * |(dominantBase * gapRatio) ^ m| := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [abs_mul]
      _ = ∑ j : Fin L, |subleadingCoeff j| * ((dominantBase * gapRatio) ^ m) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [abs_of_nonneg (pow_nonneg (mul_nonneg hBase hGap) _)]
      _ = ((dominantBase * gapRatio) ^ m) * ∑ j : Fin L, |subleadingCoeff j| := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ = dominantBase ^ (k * n) * gapRatio ^ (k * n) * ∑ j : Fin L, |subleadingCoeff j| := by
            rw [hmulpow]

end Omega.Zeta
