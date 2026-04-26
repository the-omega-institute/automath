import Omega.Zeta.XiTimePart9zWindow6HistogramFromThreeMoments
import Omega.Zeta.XiTimePart9zWindow6ThreeatomHankelFlatness

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9z-window6-involutive-thermodynamics-closure`. The
window-`6` moment triple recovers the histogram `(8,4,9)`, and the deterministic closure moment is
the associated three-atom moment sequence. -/
theorem paper_xi_time_part9z_window6_involutive_thermodynamics_closure :
    (∀ N2 N3 N4 : ℤ,
        21 = N2 + N3 + N4 →
        64 = 2 * N2 + 3 * N3 + 4 * N4 →
        212 = 4 * N2 + 9 * N3 + 16 * N4 →
        N2 = 8 ∧ N3 = 4 ∧ N4 = 9) ∧
      (∀ n : ℕ,
        xi_time_part9z_window6_threeatom_hankel_flatness_moment n =
          8 * 2 ^ n + 4 * 3 ^ n + 9 * 4 ^ n) := by
  constructor
  · intro N2 N3 N4 h0 h1 h2
    have hpack :=
      paper_xi_time_part9z_window6_histogram_from_three_moments 21 64 212 N2 N3 N4 h0 h1 h2
    exact hpack.2.2.2 ⟨rfl, rfl, rfl⟩
  · intro n
    rfl

end Omega.Zeta
