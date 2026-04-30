import Omega.Conclusion.PrimesliceFiniteDepthLedgerIncompatibility
import Omega.Conclusion.PrimesliceOmegaSupportChainCountable

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-omega-support-finite-rank-double-obstruction`.
The conclusion combines the countable increasing omega-support chain with the finite-depth
prime-slice ledger obstruction. -/
theorem paper_conclusion_omega_support_finite_rank_double_obstruction :
    (∃ supportChain : ℕ → Finset ℕ,
      (∀ N, (supportChain N).card = N + 1) ∧
        (∀ N, supportChain N ⊂ supportChain (N + 1)) ∧
        ¬ ∃ S : Finset ℕ, ∀ N, supportChain N ⊆ S) ∧
      (∀ D : conclusion_primeslice_finite_depth_ledger_incompatibility_Data,
        Function.Injective
            D.conclusion_primeslice_finite_depth_ledger_incompatibility_e ∧
          ¬ D.conclusion_primeslice_finite_depth_ledger_incompatibility_finiteRankAdditiveLedgerExists) := by
  exact ⟨paper_conclusion_primeslice_omega_support_chain_countable,
    paper_conclusion_primeslice_finite_depth_ledger_incompatibility⟩

end Omega.Conclusion
