import Omega.Conclusion.HaltingValuationWalshLedgerUnification

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-halting-dimension-binary-law`. The two halting branches of the
valuation/Walsh/ledger package have Hausdorff-dimension proxy `0` in the divergent case and
`1 / L` in every halting case. -/
theorem paper_conclusion_halting_dimension_binary_law (L : ℕ) (hL : 0 < L) :
    paper_derived_halting_valuation_walsh_ledger_unification_dimension L
        paper_derived_halting_valuation_walsh_ledger_unification_halting_state.diverges = 0 ∧
      (∀ N : ℕ,
        paper_derived_halting_valuation_walsh_ledger_unification_dimension L
            (paper_derived_halting_valuation_walsh_ledger_unification_halting_state.haltsAt N) =
          1 / (L : ℝ)) := by
  have hbranch := paper_derived_halting_valuation_walsh_ledger_unification L hL
  refine ⟨?_, ?_⟩
  · have _ :=
      hbranch paper_derived_halting_valuation_walsh_ledger_unification_halting_state.diverges
    rfl
  · intro N
    have _ :=
      hbranch (paper_derived_halting_valuation_walsh_ledger_unification_halting_state.haltsAt N)
    rfl

end Omega.Conclusion
