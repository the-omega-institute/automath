import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part9f-boundary-holographic-saturation`. -/
theorem paper_xi_time_part9f_boundary_holographic_saturation {n dG dBoundary : ℝ}
    (hn : 1 ≤ n)
    (h : ((n - 1) / n) * dG ≤ dBoundary ∧ dBoundary ≤ dG) :
    0 ≤ dG - dBoundary ∧ dG - dBoundary ≤ dG / n := by
  have hnpos : 0 < n := by linarith
  constructor
  · linarith [h.2]
  · have hlower : dG - dG / n ≤ dBoundary := by
      have hident : ((n - 1) / n) * dG = dG - dG / n := by
        field_simp [hnpos.ne']
      simpa [hident] using h.1
    linarith

end Omega.Zeta
