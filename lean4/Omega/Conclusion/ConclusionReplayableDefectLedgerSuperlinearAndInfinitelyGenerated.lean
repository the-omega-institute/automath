import Omega.Conclusion.PrimeIntegerizationSuperlinearBitlength
import Omega.Zeta.LocalizedIntegersNoUniformFinitelyGeneratedLedger

namespace Omega.Conclusion

/-- The replayable prime-addressed ledger package combines the existing superlinear bitlength lower
bound with the existing no-uniform-finitely-generated-ledger obstruction. -/
def conclusion_replayable_defect_ledger_superlinear_and_infinitely_generated_statement : Prop :=
  Omega.Conclusion.conclusion_prime_integerization_superlinear_bitlength_statement ∧
    ¬ ∃ F : ℕ → ℕ, ∀ S : Omega.Zeta.FinitePrimeLocalization,
      S.card ≤ F (Omega.Zeta.localizedIntegersCircleDimension S)

/-- Paper label:
`thm:conclusion-replayable-defect-ledger-superlinear-and-infinitely-generated`. -/
theorem paper_conclusion_replayable_defect_ledger_superlinear_and_infinitely_generated :
    conclusion_replayable_defect_ledger_superlinear_and_infinitely_generated_statement := by
  exact ⟨paper_conclusion_prime_integerization_superlinear_bitlength,
    Omega.Zeta.paper_xi_localized_integers_no_uniform_finitely_generated_ledger⟩

end Omega.Conclusion
