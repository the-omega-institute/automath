import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.KilloFoldBinEscortRenyiLogisticGeometry

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part54ab-escort-uniform-kl-bernoulli-reduction`. -/
theorem paper_xi_time_part54ab_escort_uniform_kl_bernoulli_reduction
    (a : Real) (ha : 0 ≤ a) :
    Omega.Folding.killoEscortKLDivergence 0 a =
      (1 - Omega.Folding.killoEscortTheta a) *
          Real.log ((1 - Omega.Folding.killoEscortTheta a) * Real.goldenRatio) +
        Omega.Folding.killoEscortTheta a *
          Real.log (Omega.Folding.killoEscortTheta a * Real.goldenRatio ^ 2) := by
  let _ := ha
  let θ : Real := Omega.Folding.killoEscortTheta a
  have hphi_sq : 1 + Real.goldenRatio = Real.goldenRatio ^ 2 := by
    nlinarith [Real.goldenRatio_sq]
  have htheta0 : Omega.Folding.killoEscortTheta 0 = 1 / (Real.goldenRatio ^ 2) := by
    unfold Omega.Folding.killoEscortTheta
    rw [show ((0 : ℝ) + 1) * Real.log Real.goldenRatio = Real.log Real.goldenRatio by ring]
    rw [Real.exp_log Real.goldenRatio_pos, hphi_sq]
  have hone_sub_theta0 :
      1 - (1 / (Real.goldenRatio ^ 2)) = 1 / Real.goldenRatio := by
    have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := by positivity
    calc
      1 - (1 / (Real.goldenRatio ^ 2))
          = (Real.goldenRatio ^ 2 - 1) / (Real.goldenRatio ^ 2) := by field_simp
      _ = Real.goldenRatio / (Real.goldenRatio ^ 2) := by
            rw [Real.goldenRatio_sq]
            ring
      _ = 1 / Real.goldenRatio := by field_simp [hphi_ne]
  have hdiv_theta :
      θ / (1 / (Real.goldenRatio ^ 2)) = θ * Real.goldenRatio ^ 2 := by
    have hphi_sq_ne : (Real.goldenRatio ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp [hphi_sq_ne]
  have hdiv_one_sub :
      (1 - θ) / (1 / Real.goldenRatio) = (1 - θ) * Real.goldenRatio := by
    have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := by positivity
    field_simp [hphi_ne]
  unfold Omega.Folding.killoEscortKLDivergence
  change
    θ * Real.log (θ / Omega.Folding.killoEscortTheta 0) +
        (1 - θ) * Real.log ((1 - θ) / (1 - Omega.Folding.killoEscortTheta 0)) =
      (1 - θ) * Real.log ((1 - θ) * Real.goldenRatio) +
        θ * Real.log (θ * Real.goldenRatio ^ 2)
  rw [htheta0, hone_sub_theta0, hdiv_theta, hdiv_one_sub]
  ring

end Omega.Zeta
