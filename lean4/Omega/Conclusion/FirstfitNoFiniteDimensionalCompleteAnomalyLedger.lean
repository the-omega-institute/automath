import Omega.Conclusion.NoComputableFinitePrimeCompleteInvariant

namespace Omega.Conclusion

/-- Concrete data for a finite-dimensional complete anomaly ledger obstruction. -/
structure conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_data where
  conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_word : Type
  conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_ledger : Type
  conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_decidableEq :
    DecidableEq conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_ledger
  conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_equiv :
    conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_word →
      conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_word → Prop
  conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_invariant :
    conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_word →
      conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_ledger
  conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_complete :
    ∀ w₁ w₂,
      conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_equiv w₁ w₂ ↔
        conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_invariant w₁ =
          conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_invariant w₂
  conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_undecidable :
    ¬ ∃ decide :
        conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_word →
          conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_word → Bool,
        ∀ w₁ w₂,
          decide w₁ w₂ = true ↔
            conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_equiv w₁ w₂

/-- A complete finite ledger would contradict undecidability of global first-fit equivalence. -/
def conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_statement
    (D : conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_data) : Prop :=
  ¬ ∃ Inv :
      D.conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_word →
        D.conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_ledger,
      ∀ w₁ w₂,
        D.conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_equiv w₁ w₂ ↔
          Inv w₁ = Inv w₂

/-- Paper label: `cor:conclusion-firstfit-no-finite-dimensional-complete-anomaly-ledger`. -/
theorem paper_conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger
    (D : conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_data) :
    conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_statement D := by
  letI :
      DecidableEq
        D.conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_ledger :=
    D.conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_decidableEq
  rintro ⟨Inv, hcomplete⟩
  exact paper_conclusion_no_computable_finite_prime_complete_invariant
    D.conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_equiv
    Inv
    hcomplete
    D.conclusion_firstfit_no_finite_dimensional_complete_anomaly_ledger_undecidable

end Omega.Conclusion
