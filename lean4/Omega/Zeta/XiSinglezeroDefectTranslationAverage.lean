import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.Sqrt

namespace Omega.Zeta

noncomputable section

/-- The quadratic discriminant deciding whether the single-zero defect has support. -/
def xi_singlezero_defect_translation_average_B (r a delta : ℝ) : ℝ :=
  r ^ 2 * (delta + a) ^ 2 - (delta - a) ^ 2

/-- The positive-support half-length from the translated one-variable reduction. -/
def xi_singlezero_defect_translation_average_L (r a delta : ℝ) : ℝ :=
  Real.sqrt (xi_singlezero_defect_translation_average_B r a delta / (1 - r ^ 2))

/-- Closed-form contribution of one off-line zero to the translation average. -/
def xi_singlezero_defect_translation_average_closed (r a delta : ℝ) : ℝ :=
  if 0 < xi_singlezero_defect_translation_average_B r a delta then
    2 * (delta + a) *
        Real.arctan (xi_singlezero_defect_translation_average_L r a delta / (delta + a)) -
      2 * (delta - a) *
        Real.arctan (xi_singlezero_defect_translation_average_L r a delta / (delta - a))
  else
    0

/-- The limiting mass predicted by the arctangent endpoint limits. -/
def xi_singlezero_defect_translation_average_limit (a delta : ℝ) : ℝ :=
  2 * Real.pi * min delta a

/-- Paper label: `thm:xi-singlezero-defect-translation-average`.

This registers the algebraic split used by the translation-average computation: nonpositive
`B` gives zero contribution, while positive `B` exposes the arctangent closed form, together
with the stated endpoint limiting mass. -/
theorem paper_xi_singlezero_defect_translation_average (r a delta : ℝ) :
    (xi_singlezero_defect_translation_average_B r a delta ≤ 0 →
        xi_singlezero_defect_translation_average_closed r a delta = 0) ∧
      (0 < xi_singlezero_defect_translation_average_B r a delta →
        xi_singlezero_defect_translation_average_closed r a delta =
          2 * (delta + a) *
              Real.arctan
                (xi_singlezero_defect_translation_average_L r a delta / (delta + a)) -
            2 * (delta - a) *
              Real.arctan
                (xi_singlezero_defect_translation_average_L r a delta / (delta - a))) ∧
        xi_singlezero_defect_translation_average_limit a delta = 2 * Real.pi * min delta a := by
  refine ⟨?_, ?_, ?_⟩
  · intro hB
    rw [xi_singlezero_defect_translation_average_closed, if_neg (not_lt.mpr hB)]
  · intro hB
    rw [xi_singlezero_defect_translation_average_closed, if_pos hB]
  · rfl

end

end Omega.Zeta
