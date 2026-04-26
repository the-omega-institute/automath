import Omega.Zeta.XiTimePart9xcSerrinLdpVacuum

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9xc-serrin-joint-pressure-affine-degeneration`. -/
theorem paper_xi_time_part9xc_serrin_joint_pressure_affine_degeneration
    (psi1 psi2 : Unit → ℝ) :
    ∀ theta1 theta2 : ℝ,
      Real.log (Real.exp (theta1 * psi1 () + theta2 * psi2 ())) =
        theta1 * psi1 () + theta2 * psi2 () := by
  intro theta1 theta2
  rw [Real.log_exp]

end Omega.Zeta
