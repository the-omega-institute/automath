import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-endpoint-reciprocal-arcsine-duality`. -/
theorem paper_conclusion_endpoint_reciprocal_arcsine_duality {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    let yminus := (1 - ρ) / (1 + ρ)
    let yplus := (1 + ρ) / (1 - ρ)
    yminus * yplus = 1 ∧ 0 < yminus ∧ yminus < 1 ∧ 1 < yplus := by
  have hden_plus_pos : 0 < 1 + ρ := by linarith
  have hden_minus_pos : 0 < 1 - ρ := by linarith
  have hden_plus_ne : 1 + ρ ≠ 0 := ne_of_gt hden_plus_pos
  have hden_minus_ne : 1 - ρ ≠ 0 := ne_of_gt hden_minus_pos
  dsimp
  constructor
  · field_simp [hden_plus_ne, hden_minus_ne]
  constructor
  · positivity
  constructor
  · rw [div_lt_one hden_plus_pos]
    linarith
  · rw [one_lt_div hden_minus_pos]
    linarith

end Omega.Conclusion
