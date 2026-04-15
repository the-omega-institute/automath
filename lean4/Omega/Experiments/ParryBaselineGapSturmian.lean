import Mathlib.Tactic

namespace Omega.Experiments.ParryBaselineGapSturmian

set_option maxHeartbeats 400000 in
/-- Paper-facing Sturmian-versus-Parry gap wrapper: if the folded support has size at most
    `m + 1`, every supported word has Parry mass at most the all-zero cylinder mass, and total
    variation is bounded below by the Parry mass outside the folded support, then the explicit
    lower bound follows.
    prop:parry-baseline-gap-sturmian -/
theorem paper_parry_baseline_gap_sturmian
    (m : ℕ)
    (tvDist supportMass zeroCylinderMass : ℝ)
    (hSupport : supportMass ≤ (m + 1 : ℝ) * zeroCylinderMass)
    (hTV : 1 - supportMass ≤ tvDist) :
    1 - (m + 1 : ℝ) * zeroCylinderMass ≤ tvDist := by
  linarith

end Omega.Experiments.ParryBaselineGapSturmian
