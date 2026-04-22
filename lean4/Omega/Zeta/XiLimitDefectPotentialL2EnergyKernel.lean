import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiLimitDefectPotentialRationalization

open scoped BigOperators

namespace Omega.Zeta

/-- The two coordinates of the explicit Gram representation coming from one finite defect packet. -/
def xi_limit_defect_potential_l2_energy_kernel_feature (P : XiLimitDefectPacket) : ℝ × ℝ :=
  ((P.m : ℝ) * P.γ, (P.m : ℝ) * (1 - P.δ.1))

/-- The explicit `Q`-kernel obtained after collecting the Poisson-kernel interaction terms. -/
def xi_limit_defect_potential_l2_energy_kernel_q_kernel
    (P Q : XiLimitDefectPacket) : ℝ :=
  (xi_limit_defect_potential_l2_energy_kernel_feature P).1 *
      (xi_limit_defect_potential_l2_energy_kernel_feature Q).1 +
    (xi_limit_defect_potential_l2_energy_kernel_feature P).2 *
      (xi_limit_defect_potential_l2_energy_kernel_feature Q).2

/-- The finite quadratic energy attached to the explicit `Q`-kernel. -/
def xi_limit_defect_potential_l2_energy_kernel_quadratic_form {n : ℕ}
    (packets : Fin n → XiLimitDefectPacket) (w : Fin n → ℝ) : ℝ :=
  (∑ i, w i * (xi_limit_defect_potential_l2_energy_kernel_feature (packets i)).1) ^ 2 +
    (∑ i, w i * (xi_limit_defect_potential_l2_energy_kernel_feature (packets i)).2) ^ 2

/-- Paper label: `thm:xi-limit-defect-potential-L2-energy-kernel`. The finite defect interaction
kernel is an explicit Gram kernel, so its quadratic form is a sum of two squares and is therefore
positive semidefinite. -/
theorem paper_xi_limit_defect_potential_l2_energy_kernel {n : ℕ}
    (packets : Fin n → XiLimitDefectPacket) (w : Fin n → ℝ) :
    (∀ P Q,
        xi_limit_defect_potential_l2_energy_kernel_q_kernel P Q =
          ((P.m : ℝ) * P.γ) * ((Q.m : ℝ) * Q.γ) +
            ((P.m : ℝ) * (1 - P.δ.1)) * ((Q.m : ℝ) * (1 - Q.δ.1))) ∧
      xi_limit_defect_potential_l2_energy_kernel_quadratic_form packets w =
        (∑ i, w i * (xi_limit_defect_potential_l2_energy_kernel_feature (packets i)).1) ^ 2 +
          (∑ i, w i * (xi_limit_defect_potential_l2_energy_kernel_feature (packets i)).2) ^ 2 ∧
      0 ≤ xi_limit_defect_potential_l2_energy_kernel_quadratic_form packets w := by
  refine ⟨?_, ?_, ?_⟩
  · intro P Q
    rfl
  · rfl
  · have hnonneg :
        0 ≤
          (∑ i, w i * (xi_limit_defect_potential_l2_energy_kernel_feature (packets i)).1) ^ 2 +
            (∑ i, w i * (xi_limit_defect_potential_l2_energy_kernel_feature (packets i)).2) ^ 2 := by
      nlinarith [sq_nonneg (∑ i, w i *
        (xi_limit_defect_potential_l2_energy_kernel_feature (packets i)).1),
        sq_nonneg (∑ i, w i *
          (xi_limit_defect_potential_l2_energy_kernel_feature (packets i)).2)]
    simpa [xi_limit_defect_potential_l2_energy_kernel_quadratic_form]

end Omega.Zeta
