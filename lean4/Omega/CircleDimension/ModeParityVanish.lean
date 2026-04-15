import Mathlib

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for mode parity cancellation in the Cayley--Chebyshev mode
    calculus.
    lem:mode-parity-vanish -/
theorem paper_circle_dimension_mode_parity_vanish
    (oddTotal integrandOdd integralZero : Prop)
    (hOdd : oddTotal)
    (hIntegrand : oddTotal → integrandOdd)
    (hVanish : integrandOdd → integralZero) :
    integrandOdd ∧ integralZero := by
  have hIntegrand' : integrandOdd := hIntegrand hOdd
  exact ⟨hIntegrand', hVanish hIntegrand'⟩

end Omega.CircleDimension
