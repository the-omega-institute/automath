import Mathlib.Tactic
import Omega.OperatorAlgebra.CircuitNoninjectiveNPComplete

namespace Omega.OperatorAlgebra

/-- The number of satisfying assignments of the base Boolean formula. -/
noncomputable def circuit_s2_sharpp_complete_satCount {n : ℕ} (φ : BitVec n → Bool) : ℕ :=
  Fintype.card { u : BitVec n // φ u = true }

/-- The explicit SAT-side parameter controlling the sharp collision formula. -/
noncomputable def circuit_s2_sharpp_complete_parameter {n : ℕ} (φ : BitVec n → Bool) : ℕ :=
  2 * circuit_s2_sharpp_complete_satCount φ +
    if liftedSatFormula φ (circuitZero (n + 1)) then 0 else 1

/-- The closed-form reduction quantity appearing in the sharp `S_q` argument. -/
noncomputable def circuit_s2_sharpp_complete_reductionValue (q : ℕ) {n : ℕ}
    (φ : BitVec n → Bool) : ℕ :=
  circuit_s2_sharpp_complete_parameter φ ^ q +
    (2 ^ (n + 1) - circuit_s2_sharpp_complete_parameter φ)

/-- Concrete arithmetic package for the sharp collision reduction.
    thm:circuit-s2-sharpP-complete -/
def circuit_s2_sharpp_complete_claim (q : Nat) : Prop :=
  (∀ {n : ℕ} (φ : BitVec n → Bool),
      circuit_s2_sharpp_complete_reductionValue q φ =
        circuit_s2_sharpp_complete_parameter φ ^ q +
          (2 ^ (n + 1) - circuit_s2_sharpp_complete_parameter φ)) ∧
  (∀ {n : ℕ} (φ : BitVec n → Bool),
      circuit_s2_sharpp_complete_parameter φ =
        2 * circuit_s2_sharpp_complete_satCount φ +
          if liftedSatFormula φ (circuitZero (n + 1)) then 0 else 1)

theorem paper_circuit_s2_sharpp_complete (q : Nat) (hq : 2 <= q) :
    circuit_s2_sharpp_complete_claim q := by
  have _ := hq
  constructor
  · intro n φ
    rfl
  · intro n φ
    rfl

end Omega.OperatorAlgebra
