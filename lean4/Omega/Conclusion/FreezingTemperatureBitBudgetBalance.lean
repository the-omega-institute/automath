import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-freezing-temperature-bit-budget-balance`. -/
theorem paper_conclusion_freezing_temperature_bit_budget_balance
    (alpha alpha2 g logphi log2 ac : ℝ) (hden : alpha2 < alpha)
    (hor : 0 ≤ log2 - alpha - g)
    (hac : ac * (alpha - alpha2) - (logphi - g) = 0) :
    let Gamma_or := log2 - alpha - g
    let Gamma_esc := fun a : ℝ => a * (alpha - alpha2) - (logphi - g)
    let a_bal := ac + Gamma_or / (alpha - alpha2)
    Gamma_esc a_bal = Gamma_or ∧ ac ≤ a_bal ∧
      (alpha + g < log2 → ac < a_bal) := by
  dsimp
  have hpos : 0 < alpha - alpha2 := by linarith
  have hne : alpha - alpha2 ≠ 0 := ne_of_gt hpos
  refine ⟨?_, ?_, ?_⟩
  · field_simp [hne]
    linarith [hac]
  · have hshift_nonneg : 0 ≤ (log2 - alpha - g) / (alpha - alpha2) :=
      div_nonneg hor (le_of_lt hpos)
    linarith
  · intro hstrict
    have hor_strict : 0 < log2 - alpha - g := by linarith
    have hshift_pos : 0 < (log2 - alpha - g) / (alpha - alpha2) :=
      div_pos hor_strict hpos
    linarith

end Omega.Conclusion
