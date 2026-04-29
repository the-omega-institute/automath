import Omega.Zeta.InfiniteDepthPrimeLedgerInfiniteRankObstruction

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-prime-log-faithful-layer-countable-infinite-rank`. -/
theorem paper_conclusion_prime_log_faithful_layer_countable_infinite_rank
    (D : Omega.Zeta.xi_infinite_depth_prime_ledger_infinite_rank_obstruction_data) :
    D.noFiniteGeneratedFaithfulLedger := by
  exact Omega.Zeta.paper_xi_infinite_depth_prime_ledger_infinite_rank_obstruction D

end Omega.Conclusion
