import Omega.SyncKernelWeighted.IharaGapDegeneracy

namespace Omega.SyncKernelWeighted

open IharaGapDegeneracyData

/-- Paper label: `cor:real-input-40-arity-charge-min-average`. The existing Ihara-gap
degeneracy package already gives arbitrarily small positive average densities, and the same
padding argument forces the candidate gap `deltaK` to vanish. -/
theorem paper_real_input_40_arity_charge_min_average (D : Omega.SyncKernelWeighted.IharaGapDegeneracyData) :
    (∀ ε > 0, ∃ p : Omega.SyncKernelWeighted.IharaGapDegeneracyData.loops D,
      0 < Omega.SyncKernelWeighted.IharaGapDegeneracyData.avgDensity D p ∧
        Omega.SyncKernelWeighted.IharaGapDegeneracyData.avgDensity D p < ε) ∧
      D.deltaK = 0 := by
  have hsmall : ∀ ε > 0, ∃ p : D.loops, 0 < D.avgDensity p ∧ D.avgDensity p < ε := by
    exact (paper_ihara_gap_degeneracy D).1
  have hdelta_zero : D.deltaK = 0 := by
    have hnotpos : ¬ 0 < D.deltaK := by
      intro hdelta_pos
      rcases hsmall D.deltaK hdelta_pos with ⟨p, hp_pos, hp_lt⟩
      exact not_lt_of_ge (D.deltaK_le_avgDensity p) hp_lt
    linarith [D.deltaK_nonneg]
  exact ⟨hsmall, hdelta_zero⟩

end Omega.SyncKernelWeighted
