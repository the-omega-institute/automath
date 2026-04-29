import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite-conductor audit data: a finite set of conductors, their prime supports inside
a fixed prime universe, two stage exponent profiles, and the local Ramanujan factors. -/
structure conclusion_finite_conductor_ramanujan_prime_tail_blindness_data where
  primeCount : ℕ
  auditedConductors : Finset ℕ
  primeSupport : ℕ → Finset (Fin primeCount)
  lhsStageExponent : Fin primeCount → ℕ
  rhsStageExponent : Fin primeCount → ℕ
  localRamanujanFactor : Fin primeCount → ℕ → ℤ
  supportAgreement :
    ∀ q ∈ auditedConductors, ∀ i ∈ primeSupport q, lhsStageExponent i = rhsStageExponent i

/-- The multiplicative Ramanujan audit value along the chosen finite conductor support. -/
def conclusion_finite_conductor_ramanujan_prime_tail_blindness_audit_value
    (D : conclusion_finite_conductor_ramanujan_prime_tail_blindness_data)
    (profile : Fin D.primeCount → ℕ) (q : ℕ) : ℤ :=
  Finset.prod (D.primeSupport q) fun i => D.localRamanujanFactor i (profile i)

/-- Paper-facing prime-tail blindness statement: every audited conductor sees the same
multiplicative Ramanujan audit value once the two stage exponent profiles agree on its support. -/
def conclusion_finite_conductor_ramanujan_prime_tail_blindness_statement
    (D : conclusion_finite_conductor_ramanujan_prime_tail_blindness_data) : Prop :=
  ∀ q ∈ D.auditedConductors,
    conclusion_finite_conductor_ramanujan_prime_tail_blindness_audit_value D D.lhsStageExponent q =
      conclusion_finite_conductor_ramanujan_prime_tail_blindness_audit_value D
        D.rhsStageExponent q

/-- Paper label: `thm:conclusion-finite-conductor-ramanujan-prime-tail-blindness`. On each
audited conductor `q`, the local Ramanujan factors over its finite prime support agree factor by
factor because the two stage profiles agree on that support; multiplicativity then gives equality
of the full audit values. -/
theorem paper_conclusion_finite_conductor_ramanujan_prime_tail_blindness
    (D : conclusion_finite_conductor_ramanujan_prime_tail_blindness_data) :
    conclusion_finite_conductor_ramanujan_prime_tail_blindness_statement D := by
  intro q hq
  unfold conclusion_finite_conductor_ramanujan_prime_tail_blindness_audit_value
  refine Finset.prod_congr rfl ?_
  intro i hi
  rw [D.supportAgreement q hq i hi]

end Omega.Conclusion
