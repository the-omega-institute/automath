import Omega.Zeta.XiUniqueContinuousTransverseRegister
import Omega.Zeta.InfiniteDepthPrimeLedgerInfiniteRankObstruction

namespace Omega.Zeta

/-- Paper label: `thm:xi-unique-transverse-vs-infinite-prime-rank-separation`. -/
theorem paper_xi_unique_transverse_vs_infinite_prime_rank_separation
    (register : ℝ × ℝ → ℝ)
    (hphase : ∀ radius phase₁ phase₂,
      register (radius, phase₁) = register (radius, phase₂))
    (hmono : StrictMono fun radius => register (radius, 0))
    (D : xi_infinite_depth_prime_ledger_infinite_rank_obstruction_data) :
    (xiFactorsThroughRadius register ∧ xiUniqueUpToMonotoneReparam register) ∧
      D.noFiniteGeneratedFaithfulLedger := by
  exact ⟨paper_xi_unique_continuous_transverse_register register hphase hmono,
    paper_xi_infinite_depth_prime_ledger_infinite_rank_obstruction D⟩

end Omega.Zeta
