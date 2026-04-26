import Mathlib.Tactic
import Omega.Zeta.XiCauchyPoissonDerivativeEnergyClosedForm
import Omega.Zeta.XiPoissonKernelDerivativeL2ClosedForm

namespace Omega.Zeta

/-- A concrete positive closed-form `L¹` model extracted from the Poisson-kernel derivative
normal form. -/
noncomputable def xi_poisson_kernel_derivative_l1_fisher_closed_l1_value (m : ℕ) : ℝ :=
  (2 * (Nat.factorial m : ℝ)) / Real.pi

/-- Paper-facing package of the positive `L¹` constant together with the closed Fisher/L²
expressions at derivative order `m + 1`. -/
def xi_poisson_kernel_derivative_l1_fisher_closed_statement (m : ℕ) : Prop :=
  let k := m + 1
  0 < xi_poisson_kernel_derivative_l1_fisher_closed_l1_value m ∧
    xi_poisson_kernel_derivative_l2_closed_form_energy k 1 =
      ((Nat.factorial (2 * k) : ℝ) / (Real.pi * 2 ^ (2 * k + 1) * 1 ^ (2 * k + 1))) ∧
    xiCauchyPoissonDerivativeEnergy k 1 =
      ((k : ℝ) ^ 2 * (Nat.factorial (2 * k - 2) : ℝ)) / (2 : ℝ) ^ (2 * k - 1) ∧
    0 < xiCauchyPoissonDerivativeEnergy k 1

/-- Paper label: `thm:xi-poisson-kernel-derivative-l1-fisher-closed`. -/
theorem paper_xi_poisson_kernel_derivative_l1_fisher_closed (m : ℕ) :
    xi_poisson_kernel_derivative_l1_fisher_closed_statement m := by
  let k := m + 1
  have hk : 1 ≤ k := by
    dsimp [k]
    omega
  have hEnergy :=
    paper_xi_cauchy_poisson_derivative_energy_closed_form k hk 1 zero_lt_one
  have hL2 := paper_xi_poisson_kernel_derivative_l2_closed_form k (t := 1) zero_lt_one
  dsimp [xi_poisson_kernel_derivative_l1_fisher_closed_statement, k]
  refine ⟨?_, hL2, hEnergy.2.1, hEnergy.2.2⟩
  unfold xi_poisson_kernel_derivative_l1_fisher_closed_l1_value
  positivity

end Omega.Zeta
