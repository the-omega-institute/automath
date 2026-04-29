import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.OneOrderSaturationFreezesPressureRay

namespace Omega.Conclusion

noncomputable section

/-- Concrete pressure/rate-function package for the sharp frozen/unfrozen dichotomy. -/
structure conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_data where
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_P : ℕ → ℝ
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf : ℝ
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_I : ℝ → ℝ
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_y : ℝ
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_q : ℕ
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_hq :
    2 ≤ conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_q
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_hy :
    conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_y ≤
      conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_upper :
    ∀ q : ℕ,
      1 ≤ q →
        conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_P q ≤
          Real.log 2 +
            (q - 1 : ℕ) *
              conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_zero_of_saturation :
    ∀ q0 : ℕ,
      2 ≤ q0 →
        conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_P q0 =
            Real.log 2 +
              (q0 - 1 : ℕ) *
                conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf →
          conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_I
              conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf = 0
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_linear_of_zero :
    conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_I
        conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf = 0 →
      ∀ q : ℕ,
        1 ≤ q →
          conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_P q =
            Real.log 2 +
              (q - 1 : ℕ) *
                conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_saturation_at_q :
    conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_P
        conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_q =
      Real.log 2 +
        (conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_q - 1 : ℕ) *
          conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf
  conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_legendre_formula :
    conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_P
        conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_q =
      Real.log 2 +
          ((conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_q : ℝ) - 1) *
            conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf -
        ((((conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_q : ℝ) - 1) *
            (conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf -
              conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_y)) +
          conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_I
            conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf)

namespace conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_data

/-- The attained Legendre gap in the unfrozen branch. -/
def conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_delta
    (D : conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_data) : ℝ :=
  (((D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_q : ℝ) - 1) *
      (D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf -
        D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_y)) +
    D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_I
      D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf

end conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_data

/-- Paper-facing statement: zero rate at the endpoint gives the frozen ray, while positive endpoint
rate gives a strictly positive attained Legendre gap at the chosen order. -/
def conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_statement
    (D : conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_data) : Prop :=
  (D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_I
        D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf = 0 →
      ∀ q : ℕ,
        1 ≤ q →
          D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_P q =
            Real.log 2 +
              (q - 1 : ℕ) *
                D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf) ∧
    (0 <
        D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_I
          D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf →
      ∃ δ : ℝ,
        0 < δ ∧
          δ =
            D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_delta ∧
          D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_P
              D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_q =
            Real.log 2 +
                ((D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_q : ℝ) - 1) *
                  D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf -
              δ)

/-- Paper label:
`thm:conclusion-pressure-spectrum-sharp-frozen-unfrozen-dichotomy`. -/
theorem paper_conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy
    (D : conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_data) :
    conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_statement D := by
  constructor
  · intro hzero
    exact
      (paper_conclusion_one_order_saturation_freezes_pressure_ray
        D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_P
        D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf
        (D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_I
          D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf)
        D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_upper
        D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_zero_of_saturation
        D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_linear_of_zero
        D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_hq
        D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_saturation_at_q).2
  · intro hpos
    refine ⟨D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_delta, ?_, rfl, ?_⟩
    · unfold conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_data.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_delta
      have hfactor_nonneg :
          0 ≤
            ((D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_q : ℝ) - 1) := by
        exact sub_nonneg.mpr (by exact_mod_cast
          (le_trans (by norm_num : 1 ≤ 2)
            D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_hq))
      have hdiff_nonneg :
          0 ≤
            D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_LambdaInf -
              D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_y := by
        exact sub_nonneg.mpr
          D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_hy
      exact add_pos_of_nonneg_of_pos (mul_nonneg hfactor_nonneg hdiff_nonneg) hpos
    · unfold conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_data.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_delta
      exact D.conclusion_pressure_spectrum_sharp_frozen_unfrozen_dichotomy_legendre_formula

end

end Omega.Conclusion
