import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-farey-lowtemperature-rankone-constant-collapse`. -/
theorem paper_conclusion_farey_lowtemperature_rankone_constant_collapse
    (tailBound : ℝ → ℝ)
    (hdecay : ∀ ε > 0, ∃ R > 0, ∀ s, R ≤ s → tailBound s ≤ ε) :
    ∀ ε > 0, ∃ τ0 > 0, ∀ τ, 0 < τ → τ ≤ τ0 → tailBound (1 / τ) ≤ ε := by
  intro ε hε
  rcases hdecay ε hε with ⟨R, hRpos, hR⟩
  refine ⟨1 / R, by positivity, ?_⟩
  intro τ hτpos hτle
  apply hR
  have hmul : R * τ ≤ 1 := by
    calc
      R * τ ≤ R * (1 / R) := mul_le_mul_of_nonneg_left hτle (le_of_lt hRpos)
      _ = 1 := by field_simp [ne_of_gt hRpos]
  rw [le_div_iff₀ hτpos]
  simpa [mul_comm] using hmul

end Omega.Conclusion
