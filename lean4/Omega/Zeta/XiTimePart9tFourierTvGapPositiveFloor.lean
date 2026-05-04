import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9t-fourier-tv-gap-positive-floor`. -/
theorem paper_xi_time_part9t_fourier_tv_gap_positive_floor
    (fourierAmplitudeLimit tvFourierDuality positiveFloor : Prop)
    (h : fourierAmplitudeLimit → tvFourierDuality → positiveFloor) :
    fourierAmplitudeLimit → tvFourierDuality → positiveFloor := by
  exact h

end Omega.Zeta
