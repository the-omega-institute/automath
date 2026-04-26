import Mathlib

namespace Omega.Conclusion

/-- Recursive finite-rank kernel ledger: the `m+1`st composite adds the restricted-kernel
contribution of the new stage to the previous composite total. -/
def finiteRankCompositeKernelLedger (restrictedKernelCdim : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => finiteRankCompositeKernelLedger restrictedKernelCdim m + restrictedKernelCdim m

/-- One-step finite-rank kernel chain rule encoded by the recursive ledger. -/
lemma finiteRankCompositeKernelLedger_succ (restrictedKernelCdim : ℕ → ℕ) (m : ℕ) :
    finiteRankCompositeKernelLedger restrictedKernelCdim (m + 1) =
      finiteRankCompositeKernelLedger restrictedKernelCdim m + restrictedKernelCdim m := by
  rfl

/-- The recursive kernel ledger telescopes to the sum of the stagewise restricted-kernel
contributions.
    cor:conclusion-finite-rank-ledger-telescoping-law -/
theorem paper_conclusion_finite_rank_ledger_telescoping_law
    (restrictedKernelCdim : ℕ → ℕ) (m : ℕ) :
    finiteRankCompositeKernelLedger restrictedKernelCdim m =
      Finset.sum (Finset.range m) (fun j => restrictedKernelCdim j) := by
  induction m with
  | zero =>
      simp [finiteRankCompositeKernelLedger]
  | succ m ih =>
      rw [finiteRankCompositeKernelLedger_succ, Finset.sum_range_succ, ih]

end Omega.Conclusion
