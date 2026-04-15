import Mathlib.Tactic
import Omega.Experiments.ParryBaselineGapSturmian

namespace Omega.Experiments.ParryBaselineGapSturmian

set_option maxHeartbeats 400000 in
/-- Exponential-decay corollary of the Parry/Sturmian baseline gap: once the lower bound from
    `paper_parry_baseline_gap_sturmian` is rewritten using the explicit all-zero cylinder mass, the
    complement `1 - D_TV` is bounded by an exponentially decaying term of order `m · φ^{-m}`.
    cor:parry-gap-exp -/
theorem paper_parry_gap_exp
    (m : ℕ)
    (tvDist supportMass zeroCylinderMass π0 φ : ℝ)
    (hSupport : supportMass ≤ (m + 1 : ℝ) * zeroCylinderMass)
    (hTV : 1 - supportMass ≤ tvDist)
    (hZero : zeroCylinderMass = π0 * φ * (φ⁻¹) ^ m) :
    1 - tvDist ≤ (m + 1 : ℝ) * π0 * φ * (φ⁻¹) ^ m := by
  have hGap :=
    paper_parry_baseline_gap_sturmian m tvDist supportMass zeroCylinderMass hSupport hTV
  rw [hZero] at hGap
  linarith

end Omega.Experiments.ParryBaselineGapSturmian
