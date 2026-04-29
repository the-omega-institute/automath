import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:dephys-timefiber-two-ended`. For `0 < ρ < 1`, the two Cayley endpoint
heights are positive, separated across `1`, and reciprocal. -/
theorem paper_dephys_timefiber_two_ended (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    0 < (1 - ρ) / (1 + ρ) ∧
      (1 - ρ) / (1 + ρ) < 1 ∧
      1 < (1 + ρ) / (1 - ρ) ∧
      ((1 - ρ) / (1 + ρ)) * ((1 + ρ) / (1 - ρ)) = 1 := by
  have hnum_pos : 0 < 1 - ρ := by linarith
  have hden_pos : 0 < 1 + ρ := by linarith
  have hnum_ne : 1 - ρ ≠ 0 := ne_of_gt hnum_pos
  have hden_ne : 1 + ρ ≠ 0 := ne_of_gt hden_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact div_pos hnum_pos hden_pos
  · rw [div_lt_one hden_pos]
    linarith
  · rw [one_lt_div hnum_pos]
    linarith
  · field_simp [hnum_ne, hden_ne]

end Omega.Zeta
