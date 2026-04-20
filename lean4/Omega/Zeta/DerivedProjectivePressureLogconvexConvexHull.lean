import Mathlib.Tactic
import Omega.POM.ProjectivePressureHolderLogconvex
import Omega.Zeta.XiTimePart50dcProjectivePressurePerronLogconvex

namespace Omega.Zeta

open Omega.POM

noncomputable section

/-- Concrete data for the convex-hull sandwich: a normalized pressure profile `tau`, an anchor
lower bound coming from the logarithmic radius, and a verified identification of `tau` with the
projective-pressure model from the Hölder/log-convexity package. -/
structure DerivedProjectivePressureConvexHullData where
  holderData : ProjectivePressureHolderData
  q0 : ℝ
  q1 : ℝ
  q : ℝ
  theta : ℝ
  radius : ℝ
  logRadius : ℝ
  tau : ℝ → ℝ
  htau : ∀ x, tau x = holderData.Lambda x
  hq0 : holderData.t0 = q0
  hq1 : holderData.t1 = q1
  hq : holderData.tTheta = q
  htheta : holderData.theta = theta
  hlogRadius : logRadius = Real.log radius
  logRadius_le : logRadius ≤ tau q

private def compatibleXiOffset (D : DerivedProjectivePressureConvexHullData) : Fin (0 + 1) → ℝ :=
  fun _ => Real.log D.holderData.weight - Real.log D.holderData.outputAlphabetCard

private def compatibleXiSlope (D : DerivedProjectivePressureConvexHullData) : Fin (0 + 1) → ℝ :=
  fun _ => Real.log D.holderData.weight

private lemma compatibleXi_eq_tau (D : DerivedProjectivePressureConvexHullData) (x : ℝ) :
    xiProjectivePressure 0 (compatibleXiOffset D) (compatibleXiSlope D) x = D.tau x := by
  rw [D.htau]
  have hpow : 0 < D.holderData.weight ^ (x + 1) :=
    Real.rpow_pos_of_pos D.holderData.hweight (x + 1)
  have hcard : (D.holderData.outputAlphabetCard : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt D.holderData.hcard
  simp [compatibleXiOffset, compatibleXiSlope, xiProjectivePressure, xiAffinePathWeight,
    ProjectivePressureHolderData.Lambda, ProjectivePressureHolderData.lambda, Real.log_div,
    hpow.ne', hcard, Real.log_rpow, D.holderData.hweight]
  ring

private lemma tau_midpoint_convex (D : DerivedProjectivePressureConvexHullData) (x y : ℝ) :
    D.tau ((x + y) / 2) ≤ (D.tau x + D.tau y) / 2 := by
  have hxi :=
    paper_xi_time_part50dc_projective_pressure_perron_logconvex
      0 (compatibleXiOffset D) (compatibleXiSlope D) x y
  calc
    D.tau ((x + y) / 2)
      = xiProjectivePressure 0 (compatibleXiOffset D) (compatibleXiSlope D) ((x + y) / 2) := by
          symm
          exact compatibleXi_eq_tau D ((x + y) / 2)
    _ ≤ (xiProjectivePressure 0 (compatibleXiOffset D) (compatibleXiSlope D) x +
          xiProjectivePressure 0 (compatibleXiOffset D) (compatibleXiSlope D) y) / 2 := hxi.1
    _ = (D.tau x + D.tau y) / 2 := by
          rw [compatibleXi_eq_tau D x, compatibleXi_eq_tau D y]

/-- The anchor lower bound `log r_q ≤ τ(q)` and the convex upper hull from the projective-pressure
log-convexity package together yield the claimed sandwich.
    thm:derived-projective-pressure-logconvex-convex-hull -/
theorem paper_derived_projective_pressure_logconvex_convex_hull
    (D : DerivedProjectivePressureConvexHullData) :
    D.logRadius ≤ D.tau D.q ∧
      D.tau D.q ≤ (1 - D.theta) * D.tau D.q0 + D.theta * D.tau D.q1 := by
  have _hmid := tau_midpoint_convex D D.q0 D.q1
  have hholder := paper_pom_projective_pressure_holder_logconvex D.holderData
  refine ⟨D.logRadius_le, ?_⟩
  calc
    D.tau D.q = D.holderData.Lambda D.holderData.tTheta := by
      rw [← D.hq, D.htau]
    _ ≤ (1 - D.holderData.theta) * D.holderData.Lambda D.holderData.t0 +
          D.holderData.theta * D.holderData.Lambda D.holderData.t1 := hholder.2.2
    _ = (1 - D.theta) * D.tau D.q0 + D.theta * D.tau D.q1 := by
      rw [D.htheta, D.hq0, D.hq1]
      simp [D.htau]

end

end Omega.Zeta
