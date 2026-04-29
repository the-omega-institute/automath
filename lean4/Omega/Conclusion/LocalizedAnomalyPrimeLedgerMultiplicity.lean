import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite data for the pairwise-union prime ledger.  The index set records the localized
registers, and `containsPrime p i` records whether the prime `p` appears in register `i`. -/
structure conclusion_localized_anomaly_prime_ledger_multiplicity_data where
  Register : Type
  registerFintype : Fintype Register
  registerDecidableEq : DecidableEq Register
  containsPrime : ℕ → Register → Prop
  containsPrimeDecidable : ∀ p i, Decidable (containsPrime p i)

namespace conclusion_localized_anomaly_prime_ledger_multiplicity_data

attribute [local instance] Classical.propDecidable

instance conclusion_localized_anomaly_prime_ledger_multiplicity_registerFintype
    (D : conclusion_localized_anomaly_prime_ledger_multiplicity_data) : Fintype D.Register :=
  D.registerFintype

instance conclusion_localized_anomaly_prime_ledger_multiplicity_registerDecidableEq
    (D : conclusion_localized_anomaly_prime_ledger_multiplicity_data) : DecidableEq D.Register :=
  D.registerDecidableEq

/-- Ordered pair ledger for the product kernel. -/
def conclusion_localized_anomaly_prime_ledger_multiplicity_pairLedger
    (D : conclusion_localized_anomaly_prime_ledger_multiplicity_data) :
    Finset (D.Register × D.Register) :=
  Finset.univ

/-- A pair contributes to the `p`-primary kernel exactly when one endpoint contains `p`. -/
def conclusion_localized_anomaly_prime_ledger_multiplicity_pairContainsPrime
    (D : conclusion_localized_anomaly_prime_ledger_multiplicity_data) (p : ℕ)
    (ij : D.Register × D.Register) : Prop :=
  D.containsPrime p ij.1 ∨ D.containsPrime p ij.2

/-- Pairs whose two endpoints both avoid `p`. -/
def conclusion_localized_anomaly_prime_ledger_multiplicity_pairAvoidsPrime
    (D : conclusion_localized_anomaly_prime_ledger_multiplicity_data) (p : ℕ)
    (ij : D.Register × D.Register) : Prop :=
  ¬D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairContainsPrime p ij

/-- The multiplicity formula: pairs containing `p` are all pairs minus the pairs among registers
that do not contain `p`. -/
def kernelPrimeRegisterMultiplicityFormula
    (D : conclusion_localized_anomaly_prime_ledger_multiplicity_data) : Prop :=
  ∀ p : ℕ,
    ((D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairLedger.filter
        (D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairContainsPrime p)).card) =
      D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairLedger.card -
        (D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairLedger.filter
          (D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairAvoidsPrime p)).card

end conclusion_localized_anomaly_prime_ledger_multiplicity_data

/-- Paper label: `thm:conclusion-localized-anomaly-prime-ledger-multiplicity`.  The `p`-primary
ledger multiplicity is obtained by partitioning the finite pair ledger into pairs that contain `p`
and pairs whose two endpoints avoid `p`. -/
theorem paper_conclusion_localized_anomaly_prime_ledger_multiplicity
    (D : conclusion_localized_anomaly_prime_ledger_multiplicity_data) :
    D.kernelPrimeRegisterMultiplicityFormula := by
  classical
  intro p
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairLedger)
      (p := D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairContainsPrime p)
  have hpartition' :
      (D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairLedger.filter
          (fun ij =>
            ¬D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairContainsPrime p ij)).card +
        (D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairLedger.filter
          (D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairContainsPrime p)).card =
        D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairLedger.card := by
    simpa [Nat.add_comm] using hpartition
  have havoid :
      (D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairLedger.filter
          (D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairAvoidsPrime p)).card =
        (D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairLedger.filter
          (fun ij =>
            ¬D.conclusion_localized_anomaly_prime_ledger_multiplicity_pairContainsPrime p ij)).card := by
    congr 1
    ext ij
    simp [conclusion_localized_anomaly_prime_ledger_multiplicity_data.conclusion_localized_anomaly_prime_ledger_multiplicity_pairAvoidsPrime]
  rw [havoid]
  exact Nat.eq_sub_of_add_eq' hpartition'

end Omega.Conclusion
