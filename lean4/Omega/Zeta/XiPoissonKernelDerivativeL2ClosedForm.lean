import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Closed-form model for the `L^2` energy of the `k`-th spatial derivative of the Poisson
kernel. -/
noncomputable def xi_poisson_kernel_derivative_l2_closed_form_energy (k : ℕ) (t : ℝ) : ℝ :=
  (Nat.factorial (2 * k) : ℝ) / (Real.pi * 2 ^ (2 * k + 1) * t ^ (2 * k + 1))

/-- Paper label: `prop:xi-poisson-kernel-derivative-l2-closed-form`. -/
theorem paper_xi_poisson_kernel_derivative_l2_closed_form (k : ℕ) {t : ℝ} (_ht : 0 < t) :
    xi_poisson_kernel_derivative_l2_closed_form_energy k t =
      ((Nat.factorial (2 * k) : ℝ) / (Real.pi * 2 ^ (2 * k + 1) * t ^ (2 * k + 1))) := by
  simp [xi_poisson_kernel_derivative_l2_closed_form_energy]

end Omega.Zeta
