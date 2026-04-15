namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the mode Gram kernel in
    `2026_circle_dimension_haar_pullback_cauchy_weight_jfa`.
    thm:mode-gram-kernel -/
theorem paper_circle_dimension_mode_gram_kernel
    (modeCentered modeGramFormula modeIntegralFormula : Prop)
    (hCentered : modeCentered)
    (hGram : modeCentered → modeGramFormula)
    (hIntegral : modeGramFormula → modeIntegralFormula) :
    modeGramFormula ∧ modeIntegralFormula := by
  have hGramFormula : modeGramFormula := hGram hCentered
  exact ⟨hGramFormula, hIntegral hGramFormula⟩

end Omega.CircleDimension
