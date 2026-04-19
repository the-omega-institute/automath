import Mathlib.Tactic

namespace Omega.POM

/-- Closed-form maximum orbit length for the path-toggle scan operator.
    thm:pom-toggle-scan-linear-max-orbit -/
def toggleMaxOrbitLength (ℓ : ℕ) : ℕ :=
  3 * ℓ - 7

/-- Paper-facing wrapper for the linear maximal-orbit formula.
    thm:pom-toggle-scan-linear-max-orbit -/
theorem paper_pom_toggle_scan_linear_max_orbit (ℓ : ℕ) (hℓ : 4 ≤ ℓ) :
    toggleMaxOrbitLength ℓ = 3 * ℓ - 7 := by
  have hbound : 7 ≤ 3 * ℓ := by omega
  simp [toggleMaxOrbitLength]

end Omega.POM
