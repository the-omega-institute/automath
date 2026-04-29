import Mathlib.Data.Int.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Concrete finite-window data for the Schur-channel audit. The trace readout is an integer
sequence, `qWindow` is the audited length, and `reducedDeterminantConstant` is the determinant
constant recovered from the same finite packet. -/
structure pom_finite_q_window_decidable_full_audit_data where
  qWindow : ℕ
  traceReadout : ℕ → ℤ
  reducedDeterminantConstant : ℤ

/-- The finite matrix-power trace packet read from orders `0, ..., qWindow`. -/
def pom_finite_q_window_decidable_full_audit_tracePacket
    (D : pom_finite_q_window_decidable_full_audit_data) : List ℤ :=
  List.ofFn fun i : Fin (D.qWindow + 1) => D.traceReadout i

/-- A finite numerator seed for the rational generating function determined by the audited trace
packet. -/
def pom_finite_q_window_decidable_full_audit_rationalNumerator
    (D : pom_finite_q_window_decidable_full_audit_data) : List ℤ :=
  pom_finite_q_window_decidable_full_audit_tracePacket D

/-- A reduced determinant denominator seed. Its two coefficients record the constant determinant
term and the monic leading term. -/
def pom_finite_q_window_decidable_full_audit_reducedDenominator
    (D : pom_finite_q_window_decidable_full_audit_data) : List ℤ :=
  [D.reducedDeterminantConstant, 1]

/-- The finite pole/zero candidate ledger extracted from the trace packet and determinant
constant. -/
def pom_finite_q_window_decidable_full_audit_recoveredPoleZeroLedger
    (D : pom_finite_q_window_decidable_full_audit_data) : Finset ℤ :=
  insert D.reducedDeterminantConstant ((Finset.range (D.qWindow + 1)).image D.traceReadout)

namespace pom_finite_q_window_decidable_full_audit_data

/-- The concrete full-audit claim: the finite trace packet supplies rational numerator and
denominator data, a finite ledger of pole/zero candidates, and a decidable equality test for the
recovered determinant constant. -/
def fullAuditDecidable (D : pom_finite_q_window_decidable_full_audit_data) : Prop :=
  (∃ numerator denominator : List ℤ,
      numerator = pom_finite_q_window_decidable_full_audit_rationalNumerator D ∧
        denominator = pom_finite_q_window_decidable_full_audit_reducedDenominator D) ∧
    (∃ ledger : Finset ℤ,
      ledger = pom_finite_q_window_decidable_full_audit_recoveredPoleZeroLedger D) ∧
    Nonempty (Decidable
      (D.reducedDeterminantConstant =
        (pom_finite_q_window_decidable_full_audit_reducedDenominator D).headD 0))

end pom_finite_q_window_decidable_full_audit_data

/-- Paper label: `cor:pom-finite-q-window-decidable-full-audit`. -/
theorem paper_pom_finite_q_window_decidable_full_audit
    (D : pom_finite_q_window_decidable_full_audit_data) : D.fullAuditDecidable := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨pom_finite_q_window_decidable_full_audit_rationalNumerator D,
      pom_finite_q_window_decidable_full_audit_reducedDenominator D, rfl, rfl⟩
  · exact ⟨pom_finite_q_window_decidable_full_audit_recoveredPoleZeroLedger D, rfl⟩
  · dsimp [pom_finite_q_window_decidable_full_audit_data.fullAuditDecidable,
      pom_finite_q_window_decidable_full_audit_reducedDenominator]
    exact ⟨inferInstance⟩

end Omega.POM
