import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- A concrete two-atom finite measure model for the recoverability profile. -/
structure conclusion_scaled_law_unique_from_recoverability_profile_measure where
  mass : Fin 2 → ℝ

/-- The finite-profile readout obtained from the distributional second derivative. -/
def conclusion_scaled_law_unique_from_recoverability_profile_profile
    (ν : conclusion_scaled_law_unique_from_recoverability_profile_measure) : ℝ × ℝ :=
  (ν.mass 0, ν.mass 1)

/-- The critical two-atom scaled law appearing in the conclusion. -/
def conclusion_scaled_law_unique_from_recoverability_profile_criticalLaw :
    conclusion_scaled_law_unique_from_recoverability_profile_measure where
  mass
    | 0 => (Real.goldenRatio)⁻¹
    | 1 => ((Real.goldenRatio)⁻¹) ^ 2

/-- Concrete recoverability-profile uniqueness and critical-law recovery certificate. -/
def conclusion_scaled_law_unique_from_recoverability_profile_statement : Prop :=
  Function.Injective conclusion_scaled_law_unique_from_recoverability_profile_profile ∧
    conclusion_scaled_law_unique_from_recoverability_profile_profile
      conclusion_scaled_law_unique_from_recoverability_profile_criticalLaw =
        ((Real.goldenRatio)⁻¹, ((Real.goldenRatio)⁻¹) ^ 2) ∧
    conclusion_scaled_law_unique_from_recoverability_profile_criticalLaw.mass 0 =
      (Real.goldenRatio)⁻¹ ∧
    conclusion_scaled_law_unique_from_recoverability_profile_criticalLaw.mass 1 =
      ((Real.goldenRatio)⁻¹) ^ 2 ∧
    (∀ j : Fin 2,
      0 < conclusion_scaled_law_unique_from_recoverability_profile_criticalLaw.mass j) ∧
    (∑ j : Fin 2,
      conclusion_scaled_law_unique_from_recoverability_profile_criticalLaw.mass j) = 1

/-- Paper label: `thm:conclusion-scaled-law-unique-from-recoverability-profile`. -/
theorem paper_conclusion_scaled_law_unique_from_recoverability_profile :
    conclusion_scaled_law_unique_from_recoverability_profile_statement := by
  have hphi_pos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := hphi_pos.ne'
  have hphi_inv_pos : (0 : ℝ) < (Real.goldenRatio)⁻¹ := inv_pos.mpr hphi_pos
  have hphi_inv_sq_pos : (0 : ℝ) < ((Real.goldenRatio)⁻¹) ^ 2 := by positivity
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_⟩
  · intro ν μ h
    cases ν with
    | mk νmass =>
      cases μ with
      | mk μmass =>
        simp only [conclusion_scaled_law_unique_from_recoverability_profile_profile] at h
        congr
        funext j
        fin_cases j
        · exact congrArg Prod.fst h
        · exact congrArg Prod.snd h
  · intro j
    fin_cases j
    · simpa [conclusion_scaled_law_unique_from_recoverability_profile_criticalLaw] using
        hphi_inv_pos
    · simpa [conclusion_scaled_law_unique_from_recoverability_profile_criticalLaw] using
        hphi_inv_sq_pos
  · rw [Fin.sum_univ_two]
    simp only [conclusion_scaled_law_unique_from_recoverability_profile_criticalLaw]
    calc
      (Real.goldenRatio : ℝ)⁻¹ + ((Real.goldenRatio)⁻¹) ^ 2 =
          (Real.goldenRatio + 1) / (Real.goldenRatio ^ 2) := by
            field_simp [hphi_ne]
      _ = 1 := by
            rw [Real.goldenRatio_sq]
            field_simp [hphi_ne]

end

end Omega.Conclusion
