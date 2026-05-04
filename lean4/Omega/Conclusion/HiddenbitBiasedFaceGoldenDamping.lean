import Mathlib.Tactic
import Omega.Conclusion.GoldenTopGapEqualsSdpi
import Omega.Conclusion.OddMaxfiberHiddenbitTristateCrystal
import Omega.Zeta.DerivedBinfoldTvBayesConstants

namespace Omega.Conclusion

open Filter
open scoped goldenRatio

noncomputable section

def conclusion_hiddenbit_biased_face_golden_damping_gapData :
    conclusion_golden_top_gap_equals_sdpi_data where
  even_gap_limit := conclusion_golden_top_gap_equals_sdpi_phi_inv_six_value
  sdpi_constant := conclusion_golden_top_gap_equals_sdpi_phi_inv_six_value
  phi_inv_six := conclusion_golden_top_gap_equals_sdpi_phi_inv_six_value
  odd_gap_limit := conclusion_golden_top_gap_equals_sdpi_phi_half_mul_sdpi_value
  phi_half_mul_sdpi := conclusion_golden_top_gap_equals_sdpi_phi_half_mul_sdpi_value
  conclusion_golden_top_gap_equals_sdpi_even_gap_limit_cert := rfl
  conclusion_golden_top_gap_equals_sdpi_sdpi_constant_cert := rfl
  conclusion_golden_top_gap_equals_sdpi_phi_inv_six_cert := rfl
  conclusion_golden_top_gap_equals_sdpi_odd_gap_limit_cert := rfl
  conclusion_golden_top_gap_equals_sdpi_phi_half_mul_sdpi_cert := rfl

def conclusion_hiddenbit_biased_face_golden_damping_statement : Prop :=
  ((1 / 2 : ℝ) = 1 / 2 ∨
      (1 / 2 : ℝ) = 1 / 2 + (Nat.fib (0 - 2) : ℝ) / (2 * Nat.fib (0 + 1)) ∨
        (1 / 2 : ℝ) = 1 / 2 - (Nat.fib (0 - 2) : ℝ) / (2 * Nat.fib (0 + 1))) ∧
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / (2 * Nat.fib (n + 3))) atTop
      (nhds ((1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3)) ∧
    ((1 / 2 : ℝ) + (1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3 =
      Real.goldenRatio⁻¹) ∧
    ((1 / 2 : ℝ) - (1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3 =
      (Real.goldenRatio⁻¹ : ℝ) ^ 2) ∧
    (conclusion_hiddenbit_biased_face_golden_damping_gapData.even_gap_limit =
        conclusion_hiddenbit_biased_face_golden_damping_gapData.sdpi_constant ∧
      conclusion_hiddenbit_biased_face_golden_damping_gapData.sdpi_constant =
        conclusion_hiddenbit_biased_face_golden_damping_gapData.phi_inv_six ∧
      conclusion_hiddenbit_biased_face_golden_damping_gapData.odd_gap_limit =
        conclusion_hiddenbit_biased_face_golden_damping_gapData.phi_half_mul_sdpi) ∧
    Omega.Zeta.derivedBinfoldBayesError 0 = 1 / (1 + Real.goldenRatio ^ (0 + 1))

/-- Paper label: `cor:conclusion-hiddenbit-biased-face-golden-damping`. -/
theorem paper_conclusion_hiddenbit_biased_face_golden_damping :
    conclusion_hiddenbit_biased_face_golden_damping_statement := by
  rcases paper_conclusion_odd_maxfiber_hiddenbit_tristate_crystal 0 (1 / 2 : ℝ) (Or.inl rfl)
    with ⟨htri, hlim, hplus, hminus⟩
  have hgap :=
    paper_conclusion_golden_top_gap_equals_sdpi
      conclusion_hiddenbit_biased_face_golden_damping_gapData
  rcases Omega.Zeta.paper_derived_binfold_tv_bayes_constants with ⟨hbayes, _herr⟩
  exact ⟨htri, hlim, hplus, hminus, hgap, (hbayes 0).2.2.2.2⟩

end

end Omega.Conclusion
