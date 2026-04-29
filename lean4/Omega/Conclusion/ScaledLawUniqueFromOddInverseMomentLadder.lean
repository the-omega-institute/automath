import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The two atoms recovered from the odd inverse-moment ladder. -/
def conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_sigma : Fin 2 → ℝ
  | 0 => 1
  | 1 => (Real.goldenRatio)⁻¹

/-- The recovered weights of the scaled multiplicity law. -/
def conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_weight : Fin 2 → ℝ
  | 0 => (Real.goldenRatio)⁻¹
  | 1 => ((Real.goldenRatio)⁻¹) ^ 2

/-- Coefficients of the two-pole exponential-sum generating function. -/
def conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_coeff : Fin 2 → ℝ
  | 0 => (Real.goldenRatio)⁻¹
  | 1 => (Real.goldenRatio)⁻¹

/-- Pole locations of the two-pole exponential-sum generating function. -/
def conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_pole : Fin 2 → ℝ
  | 0 => 1
  | 1 => (Real.goldenRatio) ^ 2

/-- The finite exponential-sum generating function attached to the recovered atoms. -/
def conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_atomGenerating
    (t : ℝ) : ℝ :=
  ∑ j : Fin 2,
    conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_coeff j /
      (1 - conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_pole j * t)

/-- The displayed two-simple-pole generating function. -/
def conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_twoPoleGenerating
    (t : ℝ) : ℝ :=
  (Real.goldenRatio)⁻¹ / (1 - t) +
    (Real.goldenRatio)⁻¹ / (1 - (Real.goldenRatio) ^ 2 * t)

/-- Concrete conclusion-level certificate for the two-atom scaled law recovered from the odd
inverse-moment ladder. -/
def conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_statement : Prop :=
  (∀ j : Fin 2, 0 < conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_sigma j) ∧
    (∀ j : Fin 2, 0 < conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_weight j) ∧
    (∑ j : Fin 2, conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_weight j) = 1 ∧
    conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_sigma 0 = 1 ∧
    conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_sigma 1 = (Real.goldenRatio)⁻¹ ∧
    conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_weight 0 =
      (Real.goldenRatio)⁻¹ ∧
    conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_weight 1 =
      ((Real.goldenRatio)⁻¹) ^ 2 ∧
    (∀ t : ℝ,
      conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_atomGenerating t =
        conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_twoPoleGenerating t)

/-- Paper label: `thm:conclusion-scaled-law-unique-from-odd-inverse-moment-ladder`. -/
theorem paper_conclusion_scaled_law_unique_from_odd_inverse_moment_ladder :
    conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_statement := by
  have hphi_pos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := hphi_pos.ne'
  have hphi_inv_pos : (0 : ℝ) < (Real.goldenRatio)⁻¹ := inv_pos.mpr hphi_pos
  have hphi_inv_sq_pos : (0 : ℝ) < ((Real.goldenRatio)⁻¹) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · intro j
    fin_cases j
    · simp [conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_sigma]
    · simpa [conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_sigma] using
        hphi_inv_pos
  · intro j
    fin_cases j
    · simpa [conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_weight] using
        hphi_inv_pos
    · simpa [conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_weight] using
        hphi_inv_sq_pos
  · rw [Fin.sum_univ_two]
    simp only [conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_weight]
    calc
      (Real.goldenRatio : ℝ)⁻¹ + ((Real.goldenRatio)⁻¹) ^ 2 =
          (Real.goldenRatio + 1) / (Real.goldenRatio ^ 2) := by
            field_simp [hphi_ne]
      _ = 1 := by
            rw [Real.goldenRatio_sq]
            field_simp [hphi_ne]
  · intro t
    rw [conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_atomGenerating,
      conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_twoPoleGenerating,
      Fin.sum_univ_two]
    simp [conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_coeff,
      conclusion_scaled_law_unique_from_odd_inverse_moment_ladder_pole]

end

end Omega.Conclusion
