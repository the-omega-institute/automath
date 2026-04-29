import Mathlib.Tactic
import Omega.Zeta.InfiniteDepthPrimeLedgerInfiniteRankObstruction
import Omega.Zeta.XiTimePart9wFiniteLocalizedAdditiveLedgerObstruction

namespace Omega.Zeta

/-- Concrete finite-prefix rank data for a universal off-slice prime-address ledger. The function
records how many independent prime directions are forced at each finite prefix. -/
structure xi_time_part9v_universal_offslice_ledger_not_finitely_generated_data where
  xi_time_part9v_universal_offslice_ledger_not_finitely_generated_requiredRank : ℕ → ℕ
  xi_time_part9v_universal_offslice_ledger_not_finitely_generated_prefix_rank_lower_bound :
    ∀ k : ℕ,
      k ≤ xi_time_part9v_universal_offslice_ledger_not_finitely_generated_requiredRank k

namespace xi_time_part9v_universal_offslice_ledger_not_finitely_generated_data

/-- The same prefix-rank data in the reusable infinite-prime-ledger obstruction format. -/
def xi_time_part9v_universal_offslice_ledger_not_finitely_generated_infiniteDepthData
    (D : xi_time_part9v_universal_offslice_ledger_not_finitely_generated_data) :
    xi_infinite_depth_prime_ledger_infinite_rank_obstruction_data where
  xi_infinite_depth_prime_ledger_infinite_rank_obstruction_requiredRank :=
    D.xi_time_part9v_universal_offslice_ledger_not_finitely_generated_requiredRank
  xi_infinite_depth_prime_ledger_infinite_rank_obstruction_prefix_rank_lower_bound :=
    D.xi_time_part9v_universal_offslice_ledger_not_finitely_generated_prefix_rank_lower_bound

/-- No single finite generator rank can host all universal prime-address prefixes. -/
def xi_time_part9v_universal_offslice_ledger_not_finitely_generated_noUniformFinitelyGeneratedLedger
    (D : xi_time_part9v_universal_offslice_ledger_not_finitely_generated_data) : Prop :=
  ¬ ∃ r : ℕ,
    ∀ k : ℕ,
      D.xi_time_part9v_universal_offslice_ledger_not_finitely_generated_requiredRank k ≤ r

/-- The paper-facing obstruction also carries the already verified finite-local additive ledger
obstruction used for each finite prefix. -/
def statement
    (D : xi_time_part9v_universal_offslice_ledger_not_finitely_generated_data) : Prop :=
  xi_time_part9w_finite_localized_additive_ledger_obstruction_statement ∧
    D.xi_time_part9v_universal_offslice_ledger_not_finitely_generated_noUniformFinitelyGeneratedLedger

end xi_time_part9v_universal_offslice_ledger_not_finitely_generated_data

/-- Paper label:
`thm:xi-time-part9v-universal-offslice-ledger-not-finitely-generated`. -/
theorem paper_xi_time_part9v_universal_offslice_ledger_not_finitely_generated
    (D : xi_time_part9v_universal_offslice_ledger_not_finitely_generated_data) : D.statement := by
  refine ⟨paper_xi_time_part9w_finite_localized_additive_ledger_obstruction, ?_⟩
  change
    D.xi_time_part9v_universal_offslice_ledger_not_finitely_generated_infiniteDepthData.noFiniteGeneratedFaithfulLedger
  exact paper_xi_infinite_depth_prime_ledger_infinite_rank_obstruction
    D.xi_time_part9v_universal_offslice_ledger_not_finitely_generated_infiniteDepthData

end Omega.Zeta
