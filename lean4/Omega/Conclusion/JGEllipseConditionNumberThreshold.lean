import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion.JGEllipseConditionNumberThreshold

open Real

/-- Reconstruction from the semi-axis pair is stable up to
`2 ε √N + ε²` under coordinatewise absolute error `ε`.
    thm:conclusion-jg-ellipse-condition-number-integer-threshold -/
theorem paper_conclusion_jg_ellipse_condition_number_integer_threshold
    (N : ℕ) (_hN : 2 ≤ N) (ε aTilde bTilde : ℝ)
    (ha : |aTilde - (Real.sqrt N + (Real.sqrt N)⁻¹)| ≤ ε)
    (hb : |bTilde - (Real.sqrt N - (Real.sqrt N)⁻¹)| ≤ ε) :
    let tTilde : ℝ := (aTilde + bTilde) / 2
    let NTilde : ℝ := tTilde ^ 2
    |NTilde - N| ≤ 2 * ε * Real.sqrt N + ε ^ 2 := by
  dsimp
  have hε_nonneg : 0 ≤ ε := by
    nlinarith [abs_nonneg (aTilde - (Real.sqrt N + (Real.sqrt N)⁻¹)), ha]
  have hsqrt_nonneg : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have ht :
      |(aTilde + bTilde) / 2 - Real.sqrt N| ≤ ε := by
    calc
      |(aTilde + bTilde) / 2 - Real.sqrt N|
          = |((aTilde - (Real.sqrt N + (Real.sqrt N)⁻¹)) +
              (bTilde - (Real.sqrt N - (Real.sqrt N)⁻¹))) / 2| := by
                congr 1
                ring
      _ = |(aTilde - (Real.sqrt N + (Real.sqrt N)⁻¹)) +
            (bTilde - (Real.sqrt N - (Real.sqrt N)⁻¹))| / 2 := by
              rw [abs_div]
              norm_num
      _ ≤ (|aTilde - (Real.sqrt N + (Real.sqrt N)⁻¹)| +
            |bTilde - (Real.sqrt N - (Real.sqrt N)⁻¹)|) / 2 := by
              gcongr
              exact abs_add_le _ _
      _ ≤ (ε + ε) / 2 := by
              gcongr
      _ = ε := by ring
  have hsum :
      |(aTilde + bTilde) / 2 + Real.sqrt N| ≤ ε + 2 * Real.sqrt N := by
    calc
      |(aTilde + bTilde) / 2 + Real.sqrt N|
          = |((aTilde + bTilde) / 2 - Real.sqrt N) + 2 * Real.sqrt N| := by
              congr 1
              ring
      _ ≤ |(aTilde + bTilde) / 2 - Real.sqrt N| + |2 * Real.sqrt N| := abs_add_le _ _
      _ = |(aTilde + bTilde) / 2 - Real.sqrt N| + 2 * Real.sqrt N := by
            have habs : |2 * Real.sqrt N| = 2 * Real.sqrt N := by
              rw [abs_of_nonneg]
              positivity
            rw [habs]
      _ ≤ ε + 2 * Real.sqrt N := by linarith
  have hprod :
      |(aTilde + bTilde) / 2 - Real.sqrt N| *
          |(aTilde + bTilde) / 2 + Real.sqrt N|
        ≤ ε * (ε + 2 * Real.sqrt N) := by
    exact mul_le_mul ht hsum (abs_nonneg _) hε_nonneg
  calc
    |((aTilde + bTilde) / 2) ^ 2 - N|
        = |((aTilde + bTilde) / 2) ^ 2 - (Real.sqrt N) ^ 2| := by
            rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    _ = |(aTilde + bTilde) / 2 + Real.sqrt N| *
          |(aTilde + bTilde) / 2 - Real.sqrt N| := by
            rw [sq_sub_sq, abs_mul]
    _ = |(aTilde + bTilde) / 2 - Real.sqrt N| *
          |(aTilde + bTilde) / 2 + Real.sqrt N| := by ring
    _ ≤ ε * (ε + 2 * Real.sqrt N) := hprod
    _ = 2 * ε * Real.sqrt N + ε ^ 2 := by ring

/-- If the successive semi-axis gaps are at most `2 ε`, then the midpoint observation is
compatible with both `N` and `N + 1`.
    thm:conclusion-jg-ellipse-condition-number-integer-threshold -/
theorem paper_conclusion_jg_ellipse_condition_number_overlap_criterion
    (N : ℕ) (ε : ℝ)
    (hε :
      max
        |(Real.sqrt (N + 1) + (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N + (Real.sqrt N)⁻¹)|
        |(Real.sqrt (N + 1) - (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N - (Real.sqrt N)⁻¹)|
        ≤ 2 * ε) :
    ∃ aTilde bTilde : ℝ,
      |aTilde - (Real.sqrt N + (Real.sqrt N)⁻¹)| ≤ ε ∧
      |aTilde - (Real.sqrt (N + 1) + (Real.sqrt (N + 1))⁻¹)| ≤ ε ∧
      |bTilde - (Real.sqrt N - (Real.sqrt N)⁻¹)| ≤ ε ∧
      |bTilde - (Real.sqrt (N + 1) - (Real.sqrt (N + 1))⁻¹)| ≤ ε := by
  let aN : ℝ := Real.sqrt N + (Real.sqrt N)⁻¹
  let aN1 : ℝ := Real.sqrt (N + 1) + (Real.sqrt (N + 1))⁻¹
  let bN : ℝ := Real.sqrt N - (Real.sqrt N)⁻¹
  let bN1 : ℝ := Real.sqrt (N + 1) - (Real.sqrt (N + 1))⁻¹
  have hε_nonneg : 0 ≤ ε := by
    have hmax_nonneg :
        0 ≤
          max |aN1 - aN| |bN1 - bN| := by
            exact le_trans (abs_nonneg _) (le_max_left _ _)
    nlinarith [hmax_nonneg, hε]
  refine ⟨(aN + aN1) / 2, (bN + bN1) / 2, ?_, ?_, ?_, ?_⟩
  · have hgap : |aN1 - aN| ≤ 2 * ε := le_trans (le_max_left _ _) hε
    calc
      |(aN + aN1) / 2 - aN| = |(aN1 - aN) / 2| := by
        congr 1
        ring
      _ = |aN1 - aN| / 2 := by
          rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ ε := by
        nlinarith
  · have hgap : |aN1 - aN| ≤ 2 * ε := le_trans (le_max_left _ _) hε
    calc
      |(aN + aN1) / 2 - aN1| = |(aN - aN1) / 2| := by
        congr 1
        ring
      _ = |aN - aN1| / 2 := by
          rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ = |aN1 - aN| / 2 := by rw [abs_sub_comm]
      _ ≤ ε := by
        nlinarith
  · have hgap : |bN1 - bN| ≤ 2 * ε := le_trans (le_max_right _ _) hε
    calc
      |(bN + bN1) / 2 - bN| = |(bN1 - bN) / 2| := by
        congr 1
        ring
      _ = |bN1 - bN| / 2 := by
          rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ ε := by
        nlinarith
  · have hgap : |bN1 - bN| ≤ 2 * ε := le_trans (le_max_right _ _) hε
    calc
      |(bN + bN1) / 2 - bN1| = |(bN - bN1) / 2| := by
        congr 1
        ring
      _ = |bN - bN1| / 2 := by
          rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ = |bN1 - bN| / 2 := by rw [abs_sub_comm]
      _ ≤ ε := by
        nlinarith

end Omega.Conclusion.JGEllipseConditionNumberThreshold
