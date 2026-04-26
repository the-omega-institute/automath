import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.PushforwardFullMatrix

namespace Omega.Conclusion

noncomputable section

/-- The audited folding compression ratio `2^m / F_{m+2}`. -/
def conclusion_6d_folding_golden_ellipse_realization_compression_ratio (m : ℕ) : ℝ :=
  (2 : ℝ) ^ m / Nat.fib (m + 2)

/-- The Joukowsky ellipse radius attached to the folding ratio. -/
def conclusion_6d_folding_golden_ellipse_realization_radius (m : ℕ) : ℝ :=
  Real.sqrt (conclusion_6d_folding_golden_ellipse_realization_compression_ratio m)

/-- The symbolic second moment of the Joukowsky ellipse with parameter `r`. -/
def conclusion_6d_folding_golden_ellipse_realization_second_moment (r : ℝ) : ℝ :=
  r ^ 2 + (1 / r) ^ 2

/-- Paper label: `thm:conclusion-6d-folding-golden-ellipse-realization`. The window-`6`
compression ratio is `64 / 21`, its logarithm splits into the golden exponential slope plus a
constant term, and the corresponding Joukowsky second moment is `64 / 21 + 21 / 64`. -/
theorem paper_conclusion_6d_folding_golden_ellipse_realization :
    conclusion_6d_folding_golden_ellipse_realization_compression_ratio 6 = (64 : ℝ) / 21 ∧
      Real.log (conclusion_6d_folding_golden_ellipse_realization_compression_ratio 6) =
        6 * Real.log (2 / Real.goldenRatio) + Real.log (Real.goldenRatio ^ 6 / 21) ∧
      conclusion_6d_folding_golden_ellipse_realization_radius 6 = Real.sqrt ((64 : ℝ) / 21) ∧
      conclusion_6d_folding_golden_ellipse_realization_second_moment
          (conclusion_6d_folding_golden_ellipse_realization_radius 6) =
        (64 : ℝ) / 21 + 21 / 64 := by
  have hratio :
      conclusion_6d_folding_golden_ellipse_realization_compression_ratio 6 = (64 : ℝ) / 21 := by
    unfold conclusion_6d_folding_golden_ellipse_realization_compression_ratio
    rw [Omega.Conclusion.PushforwardFullMatrix.fib8_eq_21]
    norm_num
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hbase_pos : 0 < (2 / Real.goldenRatio : ℝ) := by positivity
  have hfactor_pos : 0 < (Real.goldenRatio ^ 6 / (21 : ℝ)) := by positivity
  have hdecomp :
      conclusion_6d_folding_golden_ellipse_realization_compression_ratio 6 =
        (2 / Real.goldenRatio : ℝ) ^ 6 * (Real.goldenRatio ^ 6 / 21) := by
    rw [hratio]
    field_simp [hphi_ne]
    ring
  have hlogpow : Real.log ((2 / Real.goldenRatio : ℝ) ^ 6) = 6 * Real.log (2 / Real.goldenRatio) := by
    rw [show (2 / Real.goldenRatio : ℝ) ^ 6 = (2 / Real.goldenRatio : ℝ) ^ (6 : ℝ) by
      norm_num [Real.rpow_natCast]]
    rw [Real.log_rpow hbase_pos]
  have hradius :
      conclusion_6d_folding_golden_ellipse_realization_radius 6 = Real.sqrt ((64 : ℝ) / 21) := by
    unfold conclusion_6d_folding_golden_ellipse_realization_radius
    rw [hratio]
  have hradius_sq :
      conclusion_6d_folding_golden_ellipse_realization_radius 6 ^ 2 = (64 : ℝ) / 21 := by
    rw [hradius, Real.sq_sqrt]
    positivity
  have hradius_ne : conclusion_6d_folding_golden_ellipse_realization_radius 6 ≠ 0 := by
    rw [hradius]
    positivity
  have hinv_sq :
      ((conclusion_6d_folding_golden_ellipse_realization_radius 6)⁻¹) ^ 2 = (21 : ℝ) / 64 := by
    have hrewrite :
        ((conclusion_6d_folding_golden_ellipse_realization_radius 6)⁻¹) ^ 2 =
          (conclusion_6d_folding_golden_ellipse_realization_radius 6 ^ 2)⁻¹ := by
      field_simp [hradius_ne]
    rw [hrewrite, hradius_sq]
    norm_num
  refine ⟨hratio, ?_, hradius, ?_⟩
  · rw [hdecomp, Real.log_mul (pow_ne_zero 6 hbase_pos.ne') hfactor_pos.ne', hlogpow]
  · unfold conclusion_6d_folding_golden_ellipse_realization_second_moment
    rw [one_div, hradius_sq, hinv_sq]

end

end Omega.Conclusion
