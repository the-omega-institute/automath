import Mathlib.Tactic
import Omega.Conclusion.TruncatedSmithLedgerInfiniteIndistinguishability

namespace Omega.Conclusion

/-- Concrete data for a finite prime-stage solenoid audit: audited primes and precision bound. -/
abbrev conclusion_finite_prime_stage_solenoid_smith_incompleteness_data := Finset ℕ × ℕ

namespace conclusion_finite_prime_stage_solenoid_smith_incompleteness_data

/-- The fixed finite prime stage visible to the audit. -/
def conclusion_finite_prime_stage_solenoid_smith_incompleteness_audited_primes
    (D : conclusion_finite_prime_stage_solenoid_smith_incompleteness_data) : Finset ℕ :=
  D.1

/-- The fixed Smith-ledger precision bound visible to the audit. -/
def conclusion_finite_prime_stage_solenoid_smith_incompleteness_precision_bound
    (D : conclusion_finite_prime_stage_solenoid_smith_incompleteness_data) : ℕ :=
  D.2

/-- The finite-stage projection remembers only the chosen prime set and precision bound. -/
def conclusion_finite_prime_stage_solenoid_smith_incompleteness_truncated_ledger
    (D : conclusion_finite_prime_stage_solenoid_smith_incompleteness_data)
    (_smith : Fin 1 → ℕ) : Finset ℕ × ℕ :=
  (D.conclusion_finite_prime_stage_solenoid_smith_incompleteness_audited_primes,
    D.conclusion_finite_prime_stage_solenoid_smith_incompleteness_precision_bound)

/-- A fixed finite prime stage and fixed precision bound permit infinitely many distinct Smith
completion families with the same truncated ledger. -/
def conclusion_finite_prime_stage_solenoid_smith_incompleteness_statement
    (D : conclusion_finite_prime_stage_solenoid_smith_incompleteness_data) : Prop :=
  ∃ smithFamily : ℕ → Fin 1 → ℕ,
    Function.Injective smithFamily ∧
      ∀ r,
        D.conclusion_finite_prime_stage_solenoid_smith_incompleteness_truncated_ledger
            (smithFamily r) =
          D.conclusion_finite_prime_stage_solenoid_smith_incompleteness_truncated_ledger
            (fun _ => 1)

end conclusion_finite_prime_stage_solenoid_smith_incompleteness_data

open conclusion_finite_prime_stage_solenoid_smith_incompleteness_data

/-- Paper label: `cor:conclusion-finite-prime-stage-solenoid-smith-incompleteness`. -/
theorem paper_conclusion_finite_prime_stage_solenoid_smith_incompleteness
    (D : conclusion_finite_prime_stage_solenoid_smith_incompleteness_data) :
    D.conclusion_finite_prime_stage_solenoid_smith_incompleteness_statement := by
  unfold conclusion_finite_prime_stage_solenoid_smith_incompleteness_statement
  refine
    paper_conclusion_truncated_smith_ledger_infinite_indistinguishability
      (m := 0)
      (ledger :=
        D.conclusion_finite_prime_stage_solenoid_smith_incompleteness_truncated_ledger)
      (d := fun _ => 1)
      (ell := 2)
      ?_ ?_ ?_
  · intro r
    rfl
  · simp
  · omega

end Omega.Conclusion
