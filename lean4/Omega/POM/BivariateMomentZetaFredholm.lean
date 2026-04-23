import Mathlib.Tactic

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the finite-dimensional Fredholm determinant package.
    thm:pom-bivariate-moment-zeta-fredholm -/
theorem paper_pom_bivariate_moment_zeta_fredholm
    (traceExpansion fredholmDetRational coefficientRecovery : Prop)
    (hFredholm : traceExpansion -> fredholmDetRational)
    (hCoeff : fredholmDetRational -> coefficientRecovery) :
    traceExpansion -> (fredholmDetRational ∧ coefficientRecovery) := by
  intro hTrace
  have hFredholmDet : fredholmDetRational := hFredholm hTrace
  exact ⟨hFredholmDet, hCoeff hFredholmDet⟩

end Omega.POM
