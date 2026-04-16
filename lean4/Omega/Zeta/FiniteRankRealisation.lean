namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the finite-rank realization corollary in
    `2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta`.
    cor:finite-rank-realisation -/
theorem paper_fredholm_witt_finite_rank_realisation
    (finiteEulerProductRealisation finiteRankModel exactNonzeroRank : Prop)
    (hRealisation : finiteEulerProductRealisation)
    (hFiniteRank : finiteEulerProductRealisation → finiteRankModel)
    (hRank : finiteEulerProductRealisation → exactNonzeroRank) :
    finiteEulerProductRealisation ∧ finiteRankModel ∧ exactNonzeroRank := by
  exact ⟨hRealisation, hFiniteRank hRealisation, hRank hRealisation⟩

end Omega.Zeta
