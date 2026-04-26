import Omega.POM.DiagonalRateBinaryClosedForm
import Omega.POM.DiagonalRateUniformClosedForm

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-critical-spectrum-binary-uniform`. The binary and uniform
closed forms used in the critical-spectrum discussion are already established in the dedicated
closed-form packages, so the paper corollary is their conjunction. -/
theorem paper_pom_diagonal_rate_critical_spectrum_binary_uniform :
    pomDiagonalRateBinaryClosedForm ∧ pomDiagonalRateUniformClosedForm := by
  exact ⟨paper_pom_diagonal_rate_binary_closed_form, paper_pom_diagonal_rate_uniform_closed_form⟩

end Omega.POM
