import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

namespace Omega.Conclusion

lemma conclusion_window6_projective_long_sector_quadrupole_sign_amgm
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : 1 < x * y) : 2 < x + y := by
  nlinarith [sq_nonneg (x - y)]

lemma conclusion_window6_projective_long_sector_quadrupole_sign_neg (q : ℝ) (hq : q < 0) :
    0 < (2 : ℝ) ^ q + 4 ^ q - 2 * 3 ^ q := by
  have h2 : 0 < ((2 : ℝ) / 3) ^ q := Real.rpow_pos_of_pos (by norm_num) q
  have h4 : 0 < ((4 : ℝ) / 3) ^ q := Real.rpow_pos_of_pos (by norm_num) q
  have hprod :
      1 < ((2 : ℝ) / 3) ^ q * ((4 : ℝ) / 3) ^ q := by
    calc
      1 < ((8 : ℝ) / 9) ^ q := by
        exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num) (by norm_num) hq
      _ = ((2 : ℝ) / 3) ^ q * ((4 : ℝ) / 3) ^ q := by
        rw [← Real.mul_rpow (by positivity : 0 ≤ (2 : ℝ) / 3)
          (by positivity : 0 ≤ (4 : ℝ) / 3)]
        norm_num
  have hsum :
      2 < ((2 : ℝ) / 3) ^ q + ((4 : ℝ) / 3) ^ q :=
    conclusion_window6_projective_long_sector_quadrupole_sign_amgm h2 h4 hprod
  have h3 : 0 < (3 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) q
  have hbracket :
      0 < ((2 : ℝ) / 3) ^ q + ((4 : ℝ) / 3) ^ q - 2 := by
    linarith
  have hmul :
      0 < (3 : ℝ) ^ q *
        (((2 : ℝ) / 3) ^ q + ((4 : ℝ) / 3) ^ q - 2) := mul_pos h3 hbracket
  have hrewrite :
      (3 : ℝ) ^ q * (((2 : ℝ) / 3) ^ q + ((4 : ℝ) / 3) ^ q - 2) =
        2 ^ q + 4 ^ q - 2 * 3 ^ q := by
    rw [Real.div_rpow (by norm_num : 0 ≤ (2 : ℝ)) (by norm_num : 0 ≤ (3 : ℝ))]
    rw [Real.div_rpow (by norm_num : 0 ≤ (4 : ℝ)) (by norm_num : 0 ≤ (3 : ℝ))]
    field_simp [(ne_of_gt h3)]
  rwa [hrewrite] at hmul

lemma conclusion_window6_projective_long_sector_quadrupole_sign_between
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (2 : ℝ) ^ q + 4 ^ q - 2 * 3 ^ q < 0 := by
  have hconc := Real.strictConcaveOn_rpow hq0 hq1
  have hstrict :
      (2 : ℝ)⁻¹ * 2 ^ q + (2 : ℝ)⁻¹ * 4 ^ q < 3 ^ q := by
    have h :=
      hconc.2 (by norm_num : (2 : ℝ) ∈ Set.Ici 0) (by norm_num : (4 : ℝ) ∈ Set.Ici 0)
        (by norm_num : (2 : ℝ) ≠ 4) (by norm_num : 0 < (2 : ℝ)⁻¹)
        (by norm_num : 0 < (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1)
    norm_num [smul_eq_mul] at h ⊢
    exact h
  nlinarith

lemma conclusion_window6_projective_long_sector_quadrupole_sign_gt_one
    (q : ℝ) (hq : 1 < q) :
    0 < (2 : ℝ) ^ q + 4 ^ q - 2 * 3 ^ q := by
  have hconv := strictConvexOn_rpow hq
  have hstrict :
      3 ^ q < (2 : ℝ)⁻¹ * 2 ^ q + (2 : ℝ)⁻¹ * 4 ^ q := by
    have h :=
      hconv.2 (by norm_num : (2 : ℝ) ∈ Set.Ici 0) (by norm_num : (4 : ℝ) ∈ Set.Ici 0)
        (by norm_num : (2 : ℝ) ≠ 4) (by norm_num : 0 < (2 : ℝ)⁻¹)
        (by norm_num : 0 < (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1)
    norm_num [smul_eq_mul] at h ⊢
    exact h
  nlinarith

/-- Paper label: `cor:conclusion-window6-projective-long-sector-quadrupole-sign`. -/
theorem paper_conclusion_window6_projective_long_sector_quadrupole_sign (q : Real) :
    ((0 < q ∧ q < 1) → (2 : Real) ^ q + 4 ^ q - 2 * 3 ^ q < 0) ∧
      ((2 : Real) ^ q + 4 ^ q - 2 * 3 ^ q = 0 ↔ q = 0 ∨ q = 1) ∧
      ((q < 0 ∨ 1 < q) → 0 < (2 : Real) ^ q + 4 ^ q - 2 * 3 ^ q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hq
    exact conclusion_window6_projective_long_sector_quadrupole_sign_between q hq.1 hq.2
  · constructor
    · intro hzero
      rcases lt_trichotomy q 0 with hqneg | hq0 | hqpos
      · have hpos := conclusion_window6_projective_long_sector_quadrupole_sign_neg q hqneg
        linarith
      · exact Or.inl hq0
      · rcases lt_trichotomy q 1 with hq1 | hqeq1 | hqgt1
        · have hlt := conclusion_window6_projective_long_sector_quadrupole_sign_between q hqpos hq1
          linarith
        · exact Or.inr hqeq1
        · have hpos := conclusion_window6_projective_long_sector_quadrupole_sign_gt_one q hqgt1
          linarith
    · intro hq
      rcases hq with rfl | rfl <;> norm_num
  · intro hq
    rcases hq with hq | hq
    · exact conclusion_window6_projective_long_sector_quadrupole_sign_neg q hq
    · exact conclusion_window6_projective_long_sector_quadrupole_sign_gt_one q hq

end Omega.Conclusion
