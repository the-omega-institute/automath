namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Cayley--Chebyshev mode formula in the
    entropy-asymptotics section.
    thm:cayley-chebyshev-mode -/
theorem paper_circle_dimension_cayley_chebyshev_mode
    (modeFormula trigFormula parityLaw evenFourier oddFourier : Prop)
    (hTrig : modeFormula → trigFormula)
    (hParity : trigFormula → parityLaw)
    (hEven : trigFormula → evenFourier)
    (hOdd : trigFormula → oddFourier)
    (hMode : modeFormula) :
    trigFormula ∧ parityLaw ∧ evenFourier ∧ oddFourier := by
  have hTrig' : trigFormula := hTrig hMode
  exact ⟨hTrig', hParity hTrig', hEven hTrig', hOdd hTrig'⟩

end Omega.CircleDimension
