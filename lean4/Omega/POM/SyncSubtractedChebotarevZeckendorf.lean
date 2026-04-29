import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Omega.POM.SyncSubtractedChebotarevCapacity

namespace Omega.POM

/-- Paper label: `cor:pom-sync-subtracted-chebotarev-zeckendorf`. In the empty-ambiguity
Zeckendorf case one has `D_sync(m) = m - 1`, hence the effective depth is `n + 1 - m`. -/
theorem paper_pom_sync_subtracted_chebotarev_zeckendorf (n m groupCard : Nat)
    (lambdaValue epsilonGap deltaCheb : Real) (hm : 3 <= m) (hcard : 1 <= groupCard)
    (hlambda : 0 < lambdaValue) (hdelta : 0 < deltaCheb)
    (hRelativeError :
      (groupCard : Real) <=
        deltaCheb * lambdaValue ^ ((((1 / 2 : Real) + epsilonGap) * ((n + 1 - m : Nat) : Real))) ) :
    Real.log (groupCard : Real) <=
      pom_sync_subtracted_chebotarev_capacity_budget lambdaValue epsilonGap deltaCheb (n + 1 - m) := by
  let ambiguityShell : Finset Nat := ∅
  have hdepth : n - (m - 1) = n + 1 - m := by omega
  have hmain :=
    paper_pom_sync_subtracted_chebotarev_capacity ambiguityShell n (m - 1) m groupCard
      lambdaValue epsilonGap deltaCheb hcard hlambda hdelta (by
        simpa [ambiguityShell, pom_sync_subtracted_chebotarev_capacity_n_eff,
          pom_sync_subtracted_chebotarev_capacity_n_sync, hdepth] using hRelativeError)
  rcases hmain with ⟨_, hempty, _⟩
  have hzero : ambiguityShell.card = 0 := by simp [ambiguityShell]
  have hbound :
      Real.log (groupCard : Real) <=
        pom_sync_subtracted_chebotarev_capacity_budget lambdaValue epsilonGap deltaCheb (n - (m - 1)) :=
    hempty hzero
  simpa [hdepth, ambiguityShell] using hbound

end Omega.POM
