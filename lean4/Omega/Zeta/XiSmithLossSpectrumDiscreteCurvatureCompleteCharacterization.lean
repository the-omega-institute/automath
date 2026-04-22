import Mathlib.Data.Multiset.Basic
import Omega.Zeta.SmithPadicLossSpectrumClassification
import Omega.Zeta.XiSmithLossDiscreteCurvatureAtoms

namespace Omega.Zeta

/-- Paper label: `thm:xi-smith-loss-spectrum-discrete-curvature-complete-characterization`. -/
theorem paper_xi_smith_loss_spectrum_discrete_curvature_complete_characterization (f : ℕ → ℕ) :
    ((∃ s : Multiset ℕ, ∀ k : ℕ, f k = smithEntropy s k) ↔
      f 0 = 0 ∧
        (∀ k : ℕ, f k ≤ f (k + 1)) ∧
        (∀ k : ℕ, f (k + 2) - f (k + 1) ≤ f (k + 1) - f k) ∧
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k → f (k + 1) = f k) ∧
      ∀ s : Multiset ℕ, (∀ k : ℕ, f k = smithEntropy s k) →
        ∀ t : ℕ,
          (s.filter fun v => v = t + 1).card =
            (f (t + 1) - f t) - (f (t + 2) - f (t + 1)) := by
  refine ⟨paper_xi_smith_padic_loss_spectrum_classification f, ?_⟩
  intro s hs t
  simpa [hs t, hs (t + 1), hs (t + 2)] using
    (paper_xi_smith_loss_discrete_curvature_atoms s).2 t

end Omega.Zeta
