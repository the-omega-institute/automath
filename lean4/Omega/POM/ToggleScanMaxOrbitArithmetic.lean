import Omega.POM.ToggleScanLCMTensorization
import Omega.POM.ToggleScanLinearMaxOrbit

namespace Omega.POM

/-- Paper label: `cor:pom-toggle-scan-max-orbit-arithmetic`.  If every component of a
toggle-scan tensor product has the linear maximum orbit length `3 * ell i - 7`, then the
certified product maximum orbit lcm is the lcm of these arithmetic component lengths. -/
theorem paper_pom_toggle_scan_max_orbit_arithmetic
    (D : pom_toggle_scan_lcm_tensorization_data) (ell : D.Index → ℕ)
    (hell : ∀ i, 4 ≤ ell i)
    (hmax : ∀ i, D.maxOrbitLength i = toggleMaxOrbitLength (ell i)) :
    letI := D.indexFintype
    D.maxOrbitLCM = (Finset.univ : Finset D.Index).lcm (fun i => 3 * ell i - 7) := by
  classical
  letI := D.indexDecEq
  letI := D.indexFintype
  rw [pom_toggle_scan_lcm_tensorization_data.maxOrbitLCM]
  exact Finset.lcm_congr rfl fun i _hi => by
    rw [hmax i]
    exact paper_pom_toggle_scan_linear_max_orbit (ell i) (hell i)

end Omega.POM
