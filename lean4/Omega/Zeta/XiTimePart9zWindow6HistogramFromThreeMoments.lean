import Mathlib.Tactic
import Omega.Conclusion.Window6ThreeMomentSpectrumInversion

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9z-window6-histogram-from-three-moments`. Solving the three
moment equations on the support `{2,3,4}` recovers the histogram uniquely, and substituting the
window-`6` moment triple `(21,64,212)` gives `(8,4,9)`. -/
theorem paper_xi_time_part9z_window6_histogram_from_three_moments
    (M0 M1 M2 N2 N3 N4 : ℤ)
    (h0 : M0 = N2 + N3 + N4)
    (h1 : M1 = 2 * N2 + 3 * N3 + 4 * N4)
    (h2 : M2 = 4 * N2 + 9 * N3 + 16 * N4) :
    N2 = (12 * M0 - 7 * M1 + M2) / 2 ∧
      N3 = -8 * M0 + 6 * M1 - M2 ∧
      N4 = (6 * M0 - 5 * M1 + M2) / 2 ∧
      ((M0 = 21 ∧ M1 = 64 ∧ M2 = 212) → N2 = 8 ∧ N3 = 4 ∧ N4 = 9) := by
  rcases
      Omega.Conclusion.paper_conclusion_window6_three_moment_spectrum_inversion
        M0 M1 M2 N2 N3 N4 h0 h1 h2
    with ⟨hN2, hN3, hN4⟩
  refine ⟨hN2, hN3, hN4, ?_⟩
  rintro ⟨rfl, rfl, rfl⟩
  norm_num at hN2 hN3 hN4
  exact ⟨hN2, hN3, hN4⟩

end Omega.Zeta
