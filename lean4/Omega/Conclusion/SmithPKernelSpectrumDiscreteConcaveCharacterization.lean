import Omega.Zeta.SmithPadicLossSpectrumClassification

namespace Omega.Conclusion

/-- `thm:conclusion-smith-p-kernel-spectrum-discrete-concave-characterization` -/
theorem paper_conclusion_smith_p_kernel_spectrum_discrete_concave_characterization (f : ℕ → ℕ) :
    (∃ s : Multiset ℕ, ∀ k : ℕ, f k = Omega.Zeta.smithEntropy s k) ↔
      f 0 = 0 ∧
      (∀ k : ℕ, f k ≤ f (k + 1)) ∧
      (∀ k : ℕ, f (k + 2) - f (k + 1) ≤ f (k + 1) - f k) ∧
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → f (k + 1) = f k := by
  simpa using Omega.Zeta.paper_xi_smith_padic_loss_spectrum_classification f

end Omega.Conclusion
