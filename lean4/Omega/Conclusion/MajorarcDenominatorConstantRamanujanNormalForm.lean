import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Concrete finite denominator-layer data for the Ramanujan normal form.

The denominator-layer function is represented by a coefficient vector.  The Gram matrix is supplied
with an entrywise Ramanujan-sum expansion over finitely many modes. -/
structure conclusion_majorarc_denominator_constant_ramanujan_normal_form_data where
  conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount : ℕ
  conclusion_majorarc_denominator_constant_ramanujan_normal_form_modeCount : ℕ
  conclusion_majorarc_denominator_constant_ramanujan_normal_form_weight :
    Fin conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount → ℚ
  conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorLayerFunction :
    Fin conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount → ℚ
  conclusion_majorarc_denominator_constant_ramanujan_normal_form_coefficientVector :
    Fin conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount → ℚ
  conclusion_majorarc_denominator_constant_ramanujan_normal_form_gramMatrix :
    Fin conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount →
      Fin conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount → ℚ
  conclusion_majorarc_denominator_constant_ramanujan_normal_form_ramanujanSum :
    Fin conclusion_majorarc_denominator_constant_ramanujan_normal_form_modeCount →
      Fin conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount → ℚ
  conclusion_majorarc_denominator_constant_ramanujan_normal_form_layer_eq_coeff :
    conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorLayerFunction =
      conclusion_majorarc_denominator_constant_ramanujan_normal_form_coefficientVector
  conclusion_majorarc_denominator_constant_ramanujan_normal_form_gram_ramanujan_expansion :
    ∀ (i j :
      Fin conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount),
      conclusion_majorarc_denominator_constant_ramanujan_normal_form_gramMatrix i j =
        ∑ r : Fin conclusion_majorarc_denominator_constant_ramanujan_normal_form_modeCount,
          conclusion_majorarc_denominator_constant_ramanujan_normal_form_ramanujanSum r i *
            conclusion_majorarc_denominator_constant_ramanujan_normal_form_ramanujanSum r j

namespace conclusion_majorarc_denominator_constant_ramanujan_normal_form_data

/-- Weighted norm of a denominator-layer function. -/
def conclusion_majorarc_denominator_constant_ramanujan_normal_form_weightedLayerNorm
    (D : conclusion_majorarc_denominator_constant_ramanujan_normal_form_data) : ℚ :=
  ∑ d : Fin D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount,
    D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_weight d *
      D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorLayerFunction d *
        D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorLayerFunction d

/-- Weighted norm of the coefficient vector representing denominator-layer constants. -/
def conclusion_majorarc_denominator_constant_ramanujan_normal_form_weightedCoefficientNorm
    (D : conclusion_majorarc_denominator_constant_ramanujan_normal_form_data) : ℚ :=
  ∑ d : Fin D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount,
    D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_weight d *
      D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_coefficientVector d *
        D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_coefficientVector d

/-- The finite Gram quadratic form associated to a denominator matrix. -/
def conclusion_majorarc_denominator_constant_ramanujan_normal_form_gramQuadraticForm
    (D : conclusion_majorarc_denominator_constant_ramanujan_normal_form_data)
    (A :
      Fin D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount →
        Fin D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount →
          ℚ) : ℚ :=
  ∑ i : Fin D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount,
    ∑ j : Fin D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount,
    D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_coefficientVector i *
      A i j *
        D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_coefficientVector j

/-- The same quadratic form after entrywise expansion into Ramanujan sums. -/
def conclusion_majorarc_denominator_constant_ramanujan_normal_form_ramanujanQuadraticForm
    (D : conclusion_majorarc_denominator_constant_ramanujan_normal_form_data) : ℚ :=
  ∑ i : Fin D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount,
    ∑ j : Fin D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_denominatorCount,
      ∑ r : Fin D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_modeCount,
    D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_coefficientVector i *
      (D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_ramanujanSum r i *
        D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_ramanujanSum r j) *
          D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_coefficientVector j

/-- Denominator-layer constants are isometric to their finite coefficient vectors. -/
def weightedIsometry
    (D : conclusion_majorarc_denominator_constant_ramanujan_normal_form_data) : Prop :=
  D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_weightedLayerNorm =
    D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_weightedCoefficientNorm

/-- The finite Gram restriction equals the quadratic form obtained from Ramanujan sums. -/
def gramRestrictionRamanujanMatrix
    (D : conclusion_majorarc_denominator_constant_ramanujan_normal_form_data) : Prop :=
  D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_gramQuadraticForm
      D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_gramMatrix =
    D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_ramanujanQuadraticForm

end conclusion_majorarc_denominator_constant_ramanujan_normal_form_data

/-- Paper label: `thm:conclusion-majorarc-denominator-constant-ramanujan-normal-form`. -/
theorem paper_conclusion_majorarc_denominator_constant_ramanujan_normal_form
    (D : conclusion_majorarc_denominator_constant_ramanujan_normal_form_data) :
    D.weightedIsometry ∧ D.gramRestrictionRamanujanMatrix := by
  constructor
  · rw [
      conclusion_majorarc_denominator_constant_ramanujan_normal_form_data.weightedIsometry,
      conclusion_majorarc_denominator_constant_ramanujan_normal_form_data.conclusion_majorarc_denominator_constant_ramanujan_normal_form_weightedLayerNorm,
      conclusion_majorarc_denominator_constant_ramanujan_normal_form_data.conclusion_majorarc_denominator_constant_ramanujan_normal_form_weightedCoefficientNorm,
      D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_layer_eq_coeff]
  · rw [
      conclusion_majorarc_denominator_constant_ramanujan_normal_form_data.gramRestrictionRamanujanMatrix,
      conclusion_majorarc_denominator_constant_ramanujan_normal_form_data.conclusion_majorarc_denominator_constant_ramanujan_normal_form_gramQuadraticForm,
      conclusion_majorarc_denominator_constant_ramanujan_normal_form_data.conclusion_majorarc_denominator_constant_ramanujan_normal_form_ramanujanQuadraticForm]
    simp_rw [
      D.conclusion_majorarc_denominator_constant_ramanujan_normal_form_gram_ramanujan_expansion,
      Finset.mul_sum, Finset.sum_mul]

end Omega.Conclusion
