import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.Basic
import Omega.Folding.Window6

namespace Omega.CircleDimension

open Filter
open scoped Topology

/-- Concrete data for the audit-stable depth-limit package. The sequence `depthSeq` models the
normalized audit depth `L_Θ(Q) / log₂ Q`, the lower/upper error terms package the dyadic-prefix
lower bound and the stable-separation upper bound, and `stableSeparation` records the window-6
audit-stability notion already formalized in `Omega.Folding.Window6`. -/
structure AuditStableDepthLimitData where
  d : ℕ
  r : ℕ
  hd : 0 < d
  hr : 0 < r
  Θ : Matrix (Fin d) (Fin r) ℝ
  depthSeq : ℕ → ℝ
  stableSeparation : Omega.AuditStableBoxwise hd hr Θ
  lowerError : ℕ → ℝ
  upperError : ℕ → ℝ
  lowerBound : ∀ n, ((r : ℝ) / d) - lowerError n ≤ depthSeq n
  upperBound : ∀ n, depthSeq n ≤ ((r : ℝ) / d) + upperError n
  lowerError_tendsto : Tendsto lowerError atTop (𝓝 0)
  upperError_tendsto : Tendsto upperError atTop (𝓝 0)

namespace AuditStableDepthLimitData

/-- The critical slope predicted by the badly-approximable exponent `r / d`. -/
noncomputable def criticalSlope (D : AuditStableDepthLimitData) : ℝ :=
  (D.r : ℝ) / D.d

/-- The normalized audit depth converges to the critical slope. -/
def criticalDepthLimit (D : AuditStableDepthLimitData) : Prop :=
  Tendsto D.depthSeq atTop (𝓝 D.criticalSlope)

end AuditStableDepthLimitData

lemma tendsto_of_sandwiched_errors (x errL errU : ℕ → ℝ) (c : ℝ)
    (hlo : ∀ n, c - errL n ≤ x n)
    (hhi : ∀ n, x n ≤ c + errU n)
    (hL : Tendsto errL atTop (𝓝 0))
    (hU : Tendsto errU atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 c) := by
  have hLower : Tendsto (fun n => c - errL n) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.sub hL
  have hUpper : Tendsto (fun n => c + errU n) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add hU
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLower hUpper hlo hhi

set_option maxHeartbeats 400000 in
/-- If the dyadic-prefix lower route and the stable-separation upper route both squeeze the
normalized audit depth to `r / d`, then the depth limit exists and equals the critical slope.
    cor:cdim-audit-stable-depth-limit -/
theorem paper_cdim_audit_stable_depth_limit (D : AuditStableDepthLimitData) :
    D.criticalDepthLimit := by
  let _ := D.stableSeparation
  unfold AuditStableDepthLimitData.criticalDepthLimit AuditStableDepthLimitData.criticalSlope
  exact tendsto_of_sandwiched_errors D.depthSeq D.lowerError D.upperError ((D.r : ℝ) / D.d)
    D.lowerBound D.upperBound D.lowerError_tendsto D.upperError_tendsto

end Omega.CircleDimension
