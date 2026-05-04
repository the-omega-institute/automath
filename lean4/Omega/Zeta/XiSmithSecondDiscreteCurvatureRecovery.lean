import Omega.Zeta.XiSmithLossDiscreteCurvatureAtoms

namespace Omega.Zeta

/-- Paper label: `cor:xi-smith-second-discrete-curvature-recovery`. -/
theorem paper_xi_smith_second_discrete_curvature_recovery (s : Multiset ℕ) :
    (∀ k : ℕ,
      (s.filter fun v => v = k + 1).card =
        (Omega.Zeta.smithEntropy s (k + 1) - Omega.Zeta.smithEntropy s k) -
          (Omega.Zeta.smithEntropy s (k + 2) - Omega.Zeta.smithEntropy s (k + 1))) := by
  exact (paper_xi_smith_loss_discrete_curvature_atoms s).2

end Omega.Zeta
