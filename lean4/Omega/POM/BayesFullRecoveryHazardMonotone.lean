import Omega.POM.CompleteHomogeneousPFInfty
import Omega.POM.DiagonalRateAbsorbingDFR

namespace Omega.POM

/-- Paper label: `cor:pom-bayes-full-recovery-hazard-monotone`.
Posterior uniformization packages the Bayes full-recovery success profile into the complete
homogeneous sequence attached to the residual weights. Once that sequence is positive and
log-convex, the existing DFR criterion yields the monotonicity of the discrete hazard rate. -/
theorem paper_pom_bayes_full_recovery_hazard_monotone
    (w : List ℚ)
    (hpos : ∀ t : ℕ, 0 < completeHomogeneousSeq w t)
    (hlogconvex :
      ∀ t ≥ 1,
        completeHomogeneousSeq w t ^ 2 ≤
          completeHomogeneousSeq w (t - 1) * completeHomogeneousSeq w (t + 1)) :
    IsPFInfinity (completeHomogeneousSeq w) ∧
      ∀ t ≥ 1,
        1 - completeHomogeneousSeq w (t + 1) / completeHomogeneousSeq w t ≤
          1 - completeHomogeneousSeq w t / completeHomogeneousSeq w (t - 1) := by
  refine ⟨paper_pom_complete_homogeneous_pf_infty w, ?_⟩
  exact paper_pom_diagonal_rate_absorbing_dfr (completeHomogeneousSeq w) hpos hlogconvex

end Omega.POM
