import Omega.SPG.ScreenRankMatroidSupermodularity

namespace Omega.SPG

open Finset

/-- SPG-facing wrapper expressing the screen-kernel/top-homology audit gap package.
    thm:spg-screen-kernel-top-homology-supermodular -/
theorem paper_spg_screen_kernel_top_homology_supermodular
    {V : Type*} [DecidableEq V] (rho : Nat) (r betaTop kernelRank : Finset V → Nat)
    (hrho : ∀ s, r s ≤ rho)
    (hmono : ∀ {s t : Finset V}, s ⊆ t → r s ≤ r t)
    (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t)
    (hbeta : ∀ s, betaTop s = Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap rho r s)
    (hker : ∀ s, kernelRank s = betaTop s) :
    (∀ s,
        betaTop s = Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap rho r s ∧
          kernelRank s = betaTop s) ∧
      (∀ {s t : Finset V}, s ⊆ t → betaTop t ≤ betaTop s) ∧
      (∀ s t, betaTop s + betaTop t ≤ betaTop (s ∩ t) + betaTop (s ∪ t)) ∧
      (∀ s, kernelRank s = 0 ↔ betaTop s = 0) := by
  rcases paper_spg_screen_rank_matroid_supermodularity rho r hrho hmono hsub with
    ⟨_, _, hgapSuper, hgapMono⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact ⟨hbeta s, hker s⟩
  · intro s t hst
    simpa [hbeta s, hbeta t] using hgapMono hst
  · intro s t
    simpa [hbeta s, hbeta t, hbeta (s ∩ t), hbeta (s ∪ t)] using hgapSuper s t
  · intro s
    simpa [hker s]

end Omega.SPG
