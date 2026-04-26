import Omega.Zeta.VanvleckResidueL2LowerBound

namespace Omega.Zeta

theorem paper_xi_vanvleck_residue_energy_uniform_lb_under_radius
    (kappa : ℕ) (R denom energy : ℝ) (hR : 0 < R) (hdenom : 0 < denom)
    (hdenom_le : denom ≤ 2 * (kappa : ℝ) ^ 2 * R ^ 2)
    (henergy : (kappa : ℝ) ^ 3 * (kappa + 1) ^ 2 / (4 * denom) ≤ energy) :
    (kappa : ℝ) * (kappa + 1) ^ 2 / (8 * R ^ 2) ≤ energy := by
  have hR_sq_pos : 0 < R ^ 2 := by positivity
  have hR_den_pos : 0 < 8 * R ^ 2 := by positivity
  have hdenom4_pos : 0 < 4 * denom := by positivity
  have hcore : (1 : ℝ) / (8 * R ^ 2) ≤ (kappa : ℝ) ^ 2 / (4 * denom) := by
    refine (div_le_div_iff₀ hR_den_pos hdenom4_pos).2 ?_
    nlinarith [hdenom_le]
  have hfac_nonneg : 0 ≤ (kappa : ℝ) * (kappa + 1) ^ 2 := by positivity
  have hstep :
      (kappa : ℝ) * (kappa + 1) ^ 2 / (8 * R ^ 2) ≤
        (kappa : ℝ) ^ 3 * (kappa + 1) ^ 2 / (4 * denom) := by
    have hscaled := mul_le_mul_of_nonneg_left hcore hfac_nonneg
    simpa [div_eq_mul_inv, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hscaled
  exact le_trans hstep henergy

end Omega.Zeta
