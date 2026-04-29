import Mathlib.Tactic

namespace Omega.POM

noncomputable section

lemma pom_a2_gut_newman_threshold_root_gt_three_halves (x : ℝ) (hgt : 1 < x)
    (hroot : x ^ 6 - x ^ 5 - 4 * x ^ 4 + 8 * x ^ 3 - 6 * x ^ 2 - 4 * x + 2 = 0) :
    (3 : ℝ) / 2 < x := by
  by_contra hnot
  have hxle : x ≤ (3 : ℝ) / 2 := le_of_not_gt hnot
  have hy0 : 0 ≤ x - 1 := by linarith
  have hyhalf : x - 1 ≤ (1 : ℝ) / 2 := by linarith
  have hy2 : (x - 1) ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 :=
    pow_le_pow_left₀ hy0 hyhalf 2
  have hy3 : (x - 1) ^ 3 ≤ ((1 : ℝ) / 2) ^ 3 :=
    pow_le_pow_left₀ hy0 hyhalf 3
  have hy4 : (x - 1) ^ 4 ≤ ((1 : ℝ) / 2) ^ 4 :=
    pow_le_pow_left₀ hy0 hyhalf 4
  have hy5 : (x - 1) ^ 5 ≤ ((1 : ℝ) / 2) ^ 5 :=
    pow_le_pow_left₀ hy0 hyhalf 5
  have hy6 : (x - 1) ^ 6 ≤ ((1 : ℝ) / 2) ^ 6 :=
    pow_le_pow_left₀ hy0 hyhalf 6
  have hshift :
      x ^ 6 - x ^ 5 - 4 * x ^ 4 + 8 * x ^ 3 - 6 * x ^ 2 - 4 * x + 2 =
        (x - 1) ^ 6 + 5 * (x - 1) ^ 5 + 6 * (x - 1) ^ 4 +
          2 * (x - 1) ^ 3 - (x - 1) ^ 2 - 7 * (x - 1) - 4 := by
    ring
  have hpneg :
      x ^ 6 - x ^ 5 - 4 * x ^ 4 + 8 * x ^ 3 - 6 * x ^ 2 - 4 * x + 2 < 0 := by
    rw [hshift]
    nlinarith
  nlinarith

lemma pom_a2_gut_newman_threshold_alpha_gt_one_of_root (x : ℝ) (hgt : 1 < x)
    (hroot : x ^ 6 - x ^ 5 - 4 * x ^ 4 + 8 * x ^ 3 - 6 * x ^ 2 - 4 * x + 2 = 0) :
    1 < x * (x ^ 3 - x ^ 2 + 1) / (x ^ 2 - x + 2) := by
  have hx32 := pom_a2_gut_newman_threshold_root_gt_three_halves x hgt hroot
  have hdenpos : 0 < x ^ 2 - x + 2 := by
    have hsq : 0 ≤ (x - (1 : ℝ) / 2) ^ 2 := sq_nonneg _
    nlinarith
  have hquartic : 0 < x ^ 4 - x ^ 3 - x ^ 2 + 2 * x - 2 := by
    have hz0 : 0 ≤ x - (3 : ℝ) / 2 := by linarith
    have hz1 : 0 < x - (3 : ℝ) / 2 := by linarith
    have hz2 : 0 ≤ (x - (3 : ℝ) / 2) ^ 2 := by positivity
    have hz3 : 0 ≤ (x - (3 : ℝ) / 2) ^ 3 := by positivity
    have hz4 : 0 ≤ (x - (3 : ℝ) / 2) ^ 4 := by positivity
    have hshift :
        x ^ 4 - x ^ 3 - x ^ 2 + 2 * x - 2 =
          (x - (3 : ℝ) / 2) ^ 4 + 5 * (x - (3 : ℝ) / 2) ^ 3 +
            8 * (x - (3 : ℝ) / 2) ^ 2 + (23 / 4) * (x - (3 : ℝ) / 2) +
              7 / 16 := by
      ring
    rw [hshift]
    nlinarith
  have hmul : 1 * (x ^ 2 - x + 2) < x * (x ^ 3 - x ^ 2 + 1) := by
    nlinarith
  exact (lt_div_iff₀ hdenpos).2 hmul

/-- Paper label: `prop:pom-a2-gut-newman-threshold`. -/
theorem paper_pom_a2_gut_newman_threshold (delta : ℝ → ℝ) (alphaStar xStar : ℝ)
    (hgt : 1 < xStar)
    (hroot :
      xStar ^ 6 - xStar ^ 5 - 4 * xStar ^ 4 + 8 * xStar ^ 3 - 6 * xStar ^ 2 -
        4 * xStar + 2 = 0)
    (huniq :
      ∀ x : ℝ, 1 < x →
        x ^ 6 - x ^ 5 - 4 * x ^ 4 + 8 * x ^ 3 - 6 * x ^ 2 - 4 * x + 2 = 0 →
          x = xStar)
    (halpha : alphaStar = xStar * (xStar ^ 3 - xStar ^ 2 + 1) /
      (xStar ^ 2 - xStar + 2)) :
    1 < alphaStar ∧
      xStar ^ 6 - xStar ^ 5 - 4 * xStar ^ 4 + 8 * xStar ^ 3 - 6 * xStar ^ 2 -
        4 * xStar + 2 = 0 := by
  have _ := delta
  have _ := huniq
  refine ⟨?_, hroot⟩
  rw [halpha]
  exact pom_a2_gut_newman_threshold_alpha_gt_one_of_root xStar hgt hroot

end

end Omega.POM
