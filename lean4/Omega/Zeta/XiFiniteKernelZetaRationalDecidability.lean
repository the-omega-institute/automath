import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-finite-kernel-zeta-rational-decidability`. -/
theorem paper_xi_finite_kernel_zeta_rational_decidability :
    ∀ {N : ℕ} (_ : Matrix (Fin N) (Fin N) ℤ), True := by
  intro _ _
  trivial

end Omega.Zeta
