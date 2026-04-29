import Omega.POM.FiberMultivariateHolographicConservation

namespace Omega.Zeta

/-- Paper label: `cor:xi-fold-zminusone-cancellation-binomial-convolution`. -/
theorem paper_xi_fold_zminusone_cancellation_binomial_convolution (m : ℕ) (hm : 1 ≤ m) :
    Omega.POM.sumOverFibers (fun _ : Fin m => (-1 : ℤ)) = 0 ∧
      ∀ k, k ≤ m → ((Finset.univ : Finset (Fin m)).powersetCard k).card = Nat.choose m k := by
  constructor
  · have hproduct :=
      Omega.POM.paper_pom_fiber_multivariate_holographic_conservation (α := ℤ) m
        (fun _ : Fin m => (-1 : ℤ))
    have hm_ne_zero : m ≠ 0 := by omega
    rw [hproduct]
    simp [Omega.POM.booleanCubeProduct, hm_ne_zero]
  · intro k _hk
    simp

end Omega.Zeta
