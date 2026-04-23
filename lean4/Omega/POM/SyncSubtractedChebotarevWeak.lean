import Omega.POM.SyncSubtractedChebotarevCapacity

namespace Omega.POM

/-- Paper label: `cor:pom-sync-subtracted-chebotarev-weak`. -/
theorem paper_pom_sync_subtracted_chebotarev_weak {α : Type*} [DecidableEq α]
    (ambiguityShell : Finset α) (n nSync groupCard : ℕ) (lambdaValue epsilonGap deltaCheb : ℝ)
    (hAmb : ambiguityShell.card ≠ 0) (hcard : 1 ≤ groupCard) (hlambda : 0 < lambdaValue)
    (hdelta : 0 < deltaCheb)
    (hRelativeError :
      (groupCard : ℝ) ≤
        deltaCheb * lambdaValue ^ ((((1 / 2 : ℝ) + epsilonGap) * ((n - nSync : Nat) : ℝ)))) :
    Real.log (groupCard : ℝ) ≤
      pom_sync_subtracted_chebotarev_capacity_budget lambdaValue epsilonGap deltaCheb
        (n - nSync) := by
  have hRelativeError' :
      (groupCard : ℝ) ≤
        deltaCheb *
          lambdaValue ^
            (((1 / 2 : ℝ) + epsilonGap) *
              (pom_sync_subtracted_chebotarev_capacity_n_eff ambiguityShell n 0 nSync : ℝ)) := by
    simpa [pom_sync_subtracted_chebotarev_capacity_n_eff,
      pom_sync_subtracted_chebotarev_capacity_n_sync, hAmb] using hRelativeError
  exact
    (paper_pom_sync_subtracted_chebotarev_capacity ambiguityShell n 0 nSync groupCard
      lambdaValue epsilonGap deltaCheb hcard hlambda hdelta hRelativeError').2.2 hAmb

end Omega.POM
