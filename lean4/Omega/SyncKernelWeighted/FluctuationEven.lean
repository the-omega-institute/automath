import Omega.SyncKernelWeighted.GallavottiCohen

namespace Omega.SyncKernelWeighted

/-- Paper label: `prop:fluctuation-even`. The centered fluctuation profile inherited from the
Gallavotti--Cohen symmetry is even, so its odd part vanishes identically. -/
theorem paper_fluctuation_even
    (lam : ℝ → ℝ)
    (hSelfDual : ∀ u > 0, lam u = u * lam (1 / u))
    (hPos : ∀ θ : ℝ, 0 < lam (Real.exp θ)) :
    (∀ J : ℝ, gcCenteredCgf lam J = gcCenteredCgf lam (-J)) ∧
      gcOddPartVanishes lam := by
  exact
    ⟨(paper_sync_kernel_gallavotti_cohen lam hSelfDual hPos).2.1,
      (paper_sync_kernel_gallavotti_cohen lam hSelfDual hPos).2.2⟩

end Omega.SyncKernelWeighted
