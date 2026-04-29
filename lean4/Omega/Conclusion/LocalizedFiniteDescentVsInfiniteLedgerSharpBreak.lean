theorem paper_conclusion_localized_finite_descent_vs_infinite_ledger_sharp_break
    (finiteCoverDescentExact infiniteLedgerNoFiniteRankLinearization sharpPhaseBoundary : Prop)
    (hfinite : finiteCoverDescentExact) (hinfinite : infiniteLedgerNoFiniteRankLinearization)
    (hsharp :
      finiteCoverDescentExact -> infiniteLedgerNoFiniteRankLinearization -> sharpPhaseBoundary) :
    finiteCoverDescentExact ∧ infiniteLedgerNoFiniteRankLinearization ∧ sharpPhaseBoundary := by
  exact ⟨hfinite, hinfinite, hsharp hfinite hinfinite⟩
