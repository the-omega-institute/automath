import Omega.CircleDimension.CircleDim
import Omega.Conclusion.CdimArbitraryProfiniteKernel

namespace Omega.Conclusion

/-- Conclusion-level wrapper for the orthogonality between zero-dimensional ledgers and positive
support: arbitrary profinite kernels can be realized at fixed visible circle rank, but the
positive support itself remains torsion-free.
    thm:conclusion-zero-dimensional-ledger-positive-support-orthogonality -/
def ZeroDimLedgerPositiveSupportOrthogonalityStatement : Prop :=
  (∀ (r : ℕ) (D : ProfiniteKernelRealizationData),
      ∃ G : Type, D.circleDim G = r ∧
        Nonempty (D.pontryaginDual G ≃ D.circleFactor r × D.kernel)) ∧
    (∀ n : ℕ, 0 < n → ∀ a : ℤ, (n : ℤ) * a = 0 → a = 0)

theorem paper_conclusion_zero_dimensional_ledger_positive_support_orthogonality :
    ZeroDimLedgerPositiveSupportOrthogonalityStatement := by
  refine ⟨?_, ?_⟩
  · intro r D
    exact paper_conclusion_cdim_arbitrary_profinite_kernel r D
  · intro n hn a ha
    exact Omega.CircleDimension.paper_cdim2_noprofinite_substitute n hn a ha

end Omega.Conclusion
