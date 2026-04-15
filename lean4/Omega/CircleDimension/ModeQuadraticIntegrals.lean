import Omega.CircleDimension.ModeGramKernel

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for closed formulas for quadratic mode integrals in
    `2026_circle_dimension_haar_pullback_cauchy_weight_jfa`.
    cor:mode-quadratic-integrals -/
theorem paper_circle_dimension_mode_quadratic_integrals
    (modeCentered modeGramFormula modeIntegralFormula secantTaylorExpansion
      quadraticModeIntegralFormulas mixedParityOrthogonality : Prop)
    (hCentered : modeCentered)
    (hGram : modeCentered → modeGramFormula)
    (hIntegral : modeGramFormula → modeIntegralFormula)
    (hExpansion : modeIntegralFormula → secantTaylorExpansion)
    (hQuadratic : secantTaylorExpansion → quadraticModeIntegralFormulas)
    (hParity : quadraticModeIntegralFormulas → mixedParityOrthogonality) :
    modeGramFormula ∧ secantTaylorExpansion ∧ quadraticModeIntegralFormulas ∧
      mixedParityOrthogonality := by
  obtain ⟨hGramFormula, hIntegralFormula⟩ :=
    paper_circle_dimension_mode_gram_kernel
      modeCentered modeGramFormula modeIntegralFormula hCentered hGram hIntegral
  have hExpansionSeries : secantTaylorExpansion := hExpansion hIntegralFormula
  have hQuadraticFormulas : quadraticModeIntegralFormulas := hQuadratic hExpansionSeries
  exact ⟨hGramFormula, hExpansionSeries, hQuadraticFormulas, hParity hQuadraticFormulas⟩

end Omega.CircleDimension
