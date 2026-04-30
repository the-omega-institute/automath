import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-phase-cover-smith-spectrum-controls-branch-complexity`.
The Smith ledger equivalence transfers the ledger cardinality to the cover kernel. -/
theorem paper_conclusion_phase_cover_smith_spectrum_controls_branch_complexity
    {Kernel SmithLedger : Type*} [Fintype Kernel] [Fintype SmithLedger]
    (smithSpectrum : List Nat) (d : Nat) (hKernel : Nonempty (Kernel ≃ SmithLedger))
    (hCard : Fintype.card SmithLedger = d) (hSpectrum : smithSpectrum.prod = d) :
    Nonempty (Kernel ≃ SmithLedger) ∧ Fintype.card Kernel = d := by
  rcases hKernel with ⟨e⟩
  refine ⟨⟨e⟩, ?_⟩
  have hLedgerCardBySpectrum : Fintype.card SmithLedger = smithSpectrum.prod :=
    hCard.trans hSpectrum.symm
  exact (Fintype.card_congr e).trans (hLedgerCardBySpectrum.trans hSpectrum)

end Omega.Conclusion
