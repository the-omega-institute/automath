import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete arithmetic certificate for the endpoint `p`-adic guardrails. -/
structure dephys_padic_guardrails_endpoint_rigidity_data where
  dephys_padic_guardrails_endpoint_rigidity_p : Nat
  dephys_padic_guardrails_endpoint_rigidity_a : Nat -> Int
  dephys_padic_guardrails_endpoint_rigidity_primitive : Nat -> Int
  dephys_padic_guardrails_endpoint_rigidity_endpoint : Nat -> Int
  dephys_padic_guardrails_endpoint_rigidity_dwork_congruence :
    forall k,
      ((dephys_padic_guardrails_endpoint_rigidity_p : Int) ^ k) ∣
        dephys_padic_guardrails_endpoint_rigidity_a
            (dephys_padic_guardrails_endpoint_rigidity_p ^ k) -
          dephys_padic_guardrails_endpoint_rigidity_a
            (dephys_padic_guardrails_endpoint_rigidity_p ^ (k + 1))
  dephys_padic_guardrails_endpoint_rigidity_sparsification :
    forall n,
      not (dephys_padic_guardrails_endpoint_rigidity_p ∣ n) ->
        dephys_padic_guardrails_endpoint_rigidity_a n = 0
  dephys_padic_guardrails_endpoint_rigidity_primitive_integrality :
    forall k,
      ((dephys_padic_guardrails_endpoint_rigidity_p : Int) ^ k) ∣
        dephys_padic_guardrails_endpoint_rigidity_primitive k
  dephys_padic_guardrails_endpoint_rigidity_endpoint_supercongruence :
    forall k,
      ((dephys_padic_guardrails_endpoint_rigidity_p : Int) ^ k) ∣
        dephys_padic_guardrails_endpoint_rigidity_endpoint k
  dephys_padic_guardrails_endpoint_rigidity_odd_primitive_vanish :
    forall n,
      n % 2 = 1 ->
        dephys_padic_guardrails_endpoint_rigidity_primitive n = 0

/-- Paper-facing conjunction of the concrete endpoint guardrail checks. -/
def dephys_padic_guardrails_endpoint_rigidity_statement
    (D : dephys_padic_guardrails_endpoint_rigidity_data) : Prop :=
  (forall k,
      ((D.dephys_padic_guardrails_endpoint_rigidity_p : Int) ^ k) ∣
        D.dephys_padic_guardrails_endpoint_rigidity_a
            (D.dephys_padic_guardrails_endpoint_rigidity_p ^ k) -
          D.dephys_padic_guardrails_endpoint_rigidity_a
            (D.dephys_padic_guardrails_endpoint_rigidity_p ^ (k + 1)))
    ∧
  (forall n,
      not (D.dephys_padic_guardrails_endpoint_rigidity_p ∣ n) ->
        D.dephys_padic_guardrails_endpoint_rigidity_a n = 0)
    ∧
  (forall k,
      ((D.dephys_padic_guardrails_endpoint_rigidity_p : Int) ^ k) ∣
        D.dephys_padic_guardrails_endpoint_rigidity_primitive k)
    ∧
  (forall k,
      ((D.dephys_padic_guardrails_endpoint_rigidity_p : Int) ^ k) ∣
        D.dephys_padic_guardrails_endpoint_rigidity_endpoint k)
    ∧
  (forall n,
      n % 2 = 1 ->
        D.dephys_padic_guardrails_endpoint_rigidity_primitive n = 0)

/-- Paper label: `prop:dephys-padic-guardrails-endpoint-rigidity`. -/
theorem paper_dephys_padic_guardrails_endpoint_rigidity
    (D : dephys_padic_guardrails_endpoint_rigidity_data) :
    dephys_padic_guardrails_endpoint_rigidity_statement D := by
  exact
    ⟨D.dephys_padic_guardrails_endpoint_rigidity_dwork_congruence,
      D.dephys_padic_guardrails_endpoint_rigidity_sparsification,
      D.dephys_padic_guardrails_endpoint_rigidity_primitive_integrality,
      D.dephys_padic_guardrails_endpoint_rigidity_endpoint_supercongruence,
      D.dephys_padic_guardrails_endpoint_rigidity_odd_primitive_vanish⟩

end Omega.Zeta
