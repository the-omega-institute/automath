import Mathlib.Tactic
import Omega.Conclusion.CoordinateBundleExactMbitDropLaw
import Omega.Conclusion.FinitePrimeSolenoidTerminalObject

namespace Omega.Conclusion

/-- Archimedean finite-visible component of the split ledger. -/
def conclusion_finite_visible_archimedean_essential_prime_ledger_splitting_archimedean
    (m n : Nat) (J : Finset (Fin n)) : Nat :=
  conclusion_coordinate_bundle_exact_mbit_drop_law_visibleRank m n J

/-- Non-Archimedean essential-prime component of the split ledger. -/
def conclusion_finite_visible_archimedean_essential_prime_ledger_splitting_primeLedger
    (S : Finset ℕ) : Nat :=
  S.card

/-- Combined finite visible rank and essential-prime ledger size. -/
def conclusion_finite_visible_archimedean_essential_prime_ledger_splitting_total
    (m n : Nat) (J : Finset (Fin n)) (S : Finset ℕ) : Nat :=
  conclusion_finite_visible_archimedean_essential_prime_ledger_splitting_archimedean m n J +
    conclusion_finite_visible_archimedean_essential_prime_ledger_splitting_primeLedger S

/-- Concrete splitting package combining the finite visible Archimedean factor and the
finite-prime solenoid terminal-object exact-sequence wrapper. -/
def conclusion_finite_visible_archimedean_essential_prime_ledger_splitting_statement : Prop :=
  (∀ m n : Nat, ∀ J : Finset (Fin n), ∀ j : Fin n, j ∉ J →
    conclusion_coordinate_bundle_exact_mbit_drop_law_statement m n J j) ∧
    conclusion_finite_prime_solenoid_terminal_object_statement ∧
    (∀ (m n : Nat) (J : Finset (Fin n)) (S : Finset ℕ),
      conclusion_finite_visible_archimedean_essential_prime_ledger_splitting_total m n J S =
        conclusion_finite_visible_archimedean_essential_prime_ledger_splitting_archimedean
            m n J +
          conclusion_finite_visible_archimedean_essential_prime_ledger_splitting_primeLedger S)

/-- Paper label:
`thm:conclusion-finite-visible-archimedean-essential-prime-ledger-splitting`. -/
theorem paper_conclusion_finite_visible_archimedean_essential_prime_ledger_splitting :
    conclusion_finite_visible_archimedean_essential_prime_ledger_splitting_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro m n J j hj
    exact paper_conclusion_coordinate_bundle_exact_mbit_drop_law m n J j hj
  · exact paper_conclusion_finite_prime_solenoid_terminal_object
  · intro m n J S
    rfl

end Omega.Conclusion
