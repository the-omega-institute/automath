import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped goldenRatio

noncomputable section

def conclusion_golden_sprt_stopping_spectrum_radial_contraction_fairMode_value
    (j : ℕ) : ℝ :=
  (j + 1 : ℝ)⁻¹

def conclusion_golden_sprt_stopping_spectrum_radial_contraction_goldenRadialFactor_value :
    ℝ :=
  (Real.goldenRatio⁻¹ : ℝ)

def conclusion_golden_sprt_stopping_spectrum_radial_contraction_biasedMode_value
    (j : ℕ) : ℝ :=
  conclusion_golden_sprt_stopping_spectrum_radial_contraction_goldenRadialFactor_value *
    conclusion_golden_sprt_stopping_spectrum_radial_contraction_fairMode_value j

/-- Concrete finite spectral data for the golden SPRT stopping law. -/
structure conclusion_golden_sprt_stopping_spectrum_radial_contraction_data where
  biasedMode : ℕ → ℝ
  fairMode : ℕ → ℝ
  radialFactor : ℝ
  goldenRadialFactor : ℝ
  conclusion_golden_sprt_stopping_spectrum_radial_contraction_biasedMode_cert :
    ∀ j, biasedMode j =
      conclusion_golden_sprt_stopping_spectrum_radial_contraction_biasedMode_value j
  conclusion_golden_sprt_stopping_spectrum_radial_contraction_fairMode_cert :
    ∀ j, fairMode j =
      conclusion_golden_sprt_stopping_spectrum_radial_contraction_fairMode_value j
  conclusion_golden_sprt_stopping_spectrum_radial_contraction_radialFactor_cert :
    radialFactor =
      conclusion_golden_sprt_stopping_spectrum_radial_contraction_goldenRadialFactor_value
  conclusion_golden_sprt_stopping_spectrum_radial_contraction_goldenRadialFactor_cert :
    goldenRadialFactor =
      conclusion_golden_sprt_stopping_spectrum_radial_contraction_goldenRadialFactor_value

/-- Paper label: `cor:conclusion-golden-sprt-stopping-spectrum-radial-contraction`. -/
theorem paper_conclusion_golden_sprt_stopping_spectrum_radial_contraction
    (D : conclusion_golden_sprt_stopping_spectrum_radial_contraction_data) :
    (∀ j, D.biasedMode j = D.radialFactor * D.fairMode j) ∧
      D.radialFactor = D.goldenRadialFactor := by
  constructor
  · intro j
    calc
      D.biasedMode j =
          conclusion_golden_sprt_stopping_spectrum_radial_contraction_biasedMode_value j :=
        D.conclusion_golden_sprt_stopping_spectrum_radial_contraction_biasedMode_cert j
      _ =
          conclusion_golden_sprt_stopping_spectrum_radial_contraction_goldenRadialFactor_value *
            conclusion_golden_sprt_stopping_spectrum_radial_contraction_fairMode_value j := by
            rfl
      _ = D.radialFactor * D.fairMode j := by
        rw [D.conclusion_golden_sprt_stopping_spectrum_radial_contraction_radialFactor_cert,
          D.conclusion_golden_sprt_stopping_spectrum_radial_contraction_fairMode_cert j]
  · calc
      D.radialFactor =
          conclusion_golden_sprt_stopping_spectrum_radial_contraction_goldenRadialFactor_value :=
        D.conclusion_golden_sprt_stopping_spectrum_radial_contraction_radialFactor_cert
      _ = D.goldenRadialFactor :=
        D.conclusion_golden_sprt_stopping_spectrum_radial_contraction_goldenRadialFactor_cert.symm

end

end Omega.Conclusion
