import Mathlib.Tactic
import Omega.CircleDimension.DerivedCofinalPrimeSupportUnboundedLedgerRank

namespace Omega.Conclusion

/-- Concrete data for finite-stage phase realization and cofinal additive-ledger growth. -/
structure conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_data where
  conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_supportSize :
    ℕ → ℕ
  conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_ledgerRank :
    ℕ → ℕ
  conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_cofinalSupport :
    ∀ C, ∃ r, C <
      conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_supportSize r
  conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_rankLowerBound :
    ∀ r,
      conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_supportSize r ≤
        conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_ledgerRank r
  conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_finitePhase :
    ∀ r, ∃ code :
      Fin (conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_supportSize r) →
        Fin (2 ^
          conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_supportSize r),
      Function.Injective code

/-- Finite stages carry phase codes, but cofinal prime support forces unbounded faithful ledger
rank and excludes a uniformly bounded additive ledger family. -/
def conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_statement
    (D : conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_data) :
    Prop :=
  (∀ r, ∃ code :
      Fin (D.conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_supportSize r) →
        Fin (2 ^
          D.conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_supportSize r),
      Function.Injective code) ∧
    (∀ C, ∃ r, C <
      D.conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_ledgerRank r) ∧
      ¬ ∃ C, ∀ r,
        D.conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_ledgerRank r ≤ C

/-- Paper label:
`thm:conclusion-prime-register-finite-phase-complete-cofinal-ledger-instability`. -/
theorem paper_conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability
    (D : conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_data) :
    conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_statement D := by
  let E : Omega.CircleDimension.DerivedCofinalPrimeSupportUnboundedLedgerRankData :=
    { primeSupportSize :=
        D.conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_supportSize
      ledgerRank :=
        D.conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_ledgerRank
      cofinalPrimeSupport :=
        D.conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_cofinalSupport
      stagewiseLowerBound :=
        D.conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_rankLowerBound }
  rcases Omega.CircleDimension.paper_derived_cofinal_prime_support_unbounded_ledger_rank E with
    ⟨_, hunbounded⟩
  refine ⟨
    D.conclusion_prime_register_finite_phase_complete_cofinal_ledger_instability_finitePhase,
    hunbounded, ?_⟩
  rintro ⟨C, hC⟩
  rcases hunbounded C with ⟨r, hr⟩
  exact Nat.not_lt_of_ge (hC r) hr

end Omega.Conclusion
