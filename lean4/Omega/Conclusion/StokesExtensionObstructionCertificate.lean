import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete certificate data for the Stokes-extension obstruction: a realizable filling would
have to satisfy the chapter-local phase-sampling upper bound, while the observed certificate lies
strictly above that bound. -/
structure conclusion_stokes_extension_obstruction_certificate_data where
  sampledImageValue : ℝ
  phaseSamplingUpperBound : ℝ
  exceeds_sampling_bound : phaseSamplingUpperBound < sampledImageValue

/-- Proxy for the previously established realizability constraint: every realizable filling must
land below the phase-sampling upper bound. -/
def conclusion_stokes_extension_obstruction_certificate_realizable_image
    (D : conclusion_stokes_extension_obstruction_certificate_data) : Prop :=
  D.sampledImageValue ≤ D.phaseSamplingUpperBound

/-- A strict phase-sampling obstruction rules out any Stokes filling extending the certificate. -/
def conclusion_stokes_extension_obstruction_certificate_no_filling
    (D : conclusion_stokes_extension_obstruction_certificate_data) : Prop :=
  ¬ conclusion_stokes_extension_obstruction_certificate_realizable_image D

/-- Paper label: `cor:conclusion-stokes-extension-obstruction-certificate`. The realizable-image
upper bound is incompatible with the stated strict inequality, so no filling can exist. -/
theorem paper_conclusion_stokes_extension_obstruction_certificate
    (D : conclusion_stokes_extension_obstruction_certificate_data) :
    conclusion_stokes_extension_obstruction_certificate_no_filling D := by
  intro hRealizable
  exact not_le_of_gt D.exceeds_sampling_bound hRealizable

end Omega.Conclusion
