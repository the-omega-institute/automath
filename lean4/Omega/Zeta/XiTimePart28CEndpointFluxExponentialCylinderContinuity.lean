import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part28c-endpoint-flux-exponential-cylinder-continuity`. -/
theorem paper_xi_time_part28c_endpoint_flux_exponential_cylinder_continuity
    (N : ℕ) (PhiA PhiB F C q : ℝ) (hA : |PhiA - F| ≤ C * q ^ N)
    (hB : |PhiB - F| ≤ C * q ^ N) :
    |PhiA - PhiB| ≤ 2 * C * q ^ N := by
  have hB' : |F - PhiB| ≤ C * q ^ N := by
    simpa [abs_sub_comm] using hB
  calc
    |PhiA - PhiB| = |(PhiA - F) + (F - PhiB)| := by ring_nf
    _ ≤ |PhiA - F| + |F - PhiB| := abs_add_le _ _
    _ ≤ C * q ^ N + C * q ^ N := add_le_add hA hB'
    _ = 2 * C * q ^ N := by ring

end Omega.Zeta
