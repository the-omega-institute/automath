import Omega.Conclusion.ConclusionHookChannelGeneratingPolynomialFactorization

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-pure-phase-hook-family-complete-recovery`. -/
theorem paper_conclusion_pure_phase_hook_family_complete_recovery (q : ℕ) (c c' : ℕ → ℕ)
    (hH :
      conclusion_hook_channel_generating_polynomial_factorization_hook_generating_polynomial q c' =
        conclusion_hook_channel_generating_polynomial_factorization_hook_generating_polynomial q c) :
    ∀ r, r ≤ q → c' r = c r := by
  exact (paper_conclusion_hook_channel_generating_polynomial_factorization q c).2 c' hH

end Omega.Conclusion
