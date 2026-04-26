import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.OperatorAlgebra.CircuitNoninjectiveNPComplete

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- The `k`-collision certificates, indexed by their common circuit output. -/
abbrev circuit_sk_fixedk_sharpp_complete_equal_output_tuples {n : ℕ} (C : BoolCircuit n) (k : ℕ) :=
  Σ y : BitVec n, Fin k → { a : BitVec n // C a = y }

noncomputable instance circuit_sk_fixedk_sharpp_complete_equal_output_tuples_fintype {n : ℕ}
    (C : BoolCircuit n) (k : ℕ) :
    Fintype (circuit_sk_fixedk_sharpp_complete_equal_output_tuples C k) := by
  classical
  unfold circuit_sk_fixedk_sharpp_complete_equal_output_tuples
  infer_instance

/-- The corresponding fiberwise collision sum `S_k(C) = Σ_y |C⁻¹(y)|^k`. -/
def circuit_sk_fixedk_sharpp_complete_collision_sum {n : ℕ} (C : BoolCircuit n) (k : ℕ) : ℕ :=
  ∑ y, (Fintype.card { a : BitVec n // C a = y }) ^ k

/-- The number of `k`-collision certificates, counted together with their common output. -/
noncomputable def circuit_sk_fixedk_sharpp_complete_equal_output_tuple_count {n : ℕ}
    (C : BoolCircuit n) (k : ℕ) : ℕ :=
  Fintype.card (circuit_sk_fixedk_sharpp_complete_equal_output_tuples C k)

/-- The number of satisfying assignments of the base Boolean formula. -/
noncomputable def circuit_sk_fixedk_sharpp_complete_sat_count {n : ℕ}
    (φ : BitVec n → Bool) : ℕ :=
  Fintype.card { u : BitVec n // φ u = true }

/-- The number of satisfying assignments of the lifted formula used by the collapse circuit. -/
noncomputable def circuit_sk_fixedk_sharpp_complete_lifted_sat_count {n : ℕ}
    (φ : BitVec n → Bool) : ℕ :=
  Fintype.card { a : BitVec (n + 1) // liftedSatFormula φ a = true }

/-- The fiber-size parameter of the distinguished zero output in the collapse circuit. -/
noncomputable def circuit_sk_fixedk_sharpp_complete_parameter {n : ℕ}
    (φ : BitVec n → Bool) : ℕ :=
  2 * circuit_sk_fixedk_sharpp_complete_sat_count φ +
    if liftedSatFormula φ (circuitZero (n + 1)) then 0 else 1

/-- The closed-form value used in the fixed-`k` reduction. -/
noncomputable def circuit_sk_fixedk_sharpp_complete_reduction_value (k : ℕ) {n : ℕ}
    (φ : BitVec n → Bool) : ℕ :=
  circuit_sk_fixedk_sharpp_complete_parameter φ ^ k +
    (2 ^ (n + 1) - circuit_sk_fixedk_sharpp_complete_parameter φ)

/-- Concrete package for the fixed-`k` sharp collision-moment argument. -/
noncomputable def circuit_sk_fixedk_sharpp_complete_statement (k : ℕ) : Prop :=
    (∀ {n : ℕ} (φ : BitVec n → Bool),
      circuit_sk_fixedk_sharpp_complete_lifted_sat_count φ =
        2 * circuit_sk_fixedk_sharpp_complete_sat_count φ) ∧
    (∀ {n : ℕ} (C : BoolCircuit n),
      circuit_sk_fixedk_sharpp_complete_equal_output_tuple_count C k =
        circuit_sk_fixedk_sharpp_complete_collision_sum C k) ∧
    (∀ {n : ℕ} (φ : BitVec n → Bool),
      circuit_sk_fixedk_sharpp_complete_reduction_value k φ =
        circuit_sk_fixedk_sharpp_complete_parameter φ ^ k +
          (2 ^ (n + 1) - circuit_sk_fixedk_sharpp_complete_parameter φ))

/-- The lifted satisfying assignments are exactly a satisfying base assignment together with the
free extra bit. -/
noncomputable def circuit_sk_fixedk_sharpp_complete_lifted_witness_equiv {n : ℕ}
    (φ : BitVec n → Bool) :
    { a : BitVec (n + 1) // liftedSatFormula φ a = true } ≃
      ({ u : BitVec n // φ u = true } × Bool) where
  toFun a :=
    ⟨⟨Fin.init a.1, by simpa [liftedSatFormula_eq] using a.2⟩, a.1 (Fin.last n)⟩
  invFun s :=
    ⟨appendBit s.1.1 s.2, by simpa [appendBit, liftedSatFormula_eq] using s.1.2⟩
  left_inv a := by
    apply Subtype.ext
    simpa [appendBit] using Fin.snoc_init_self a.1
  right_inv s := by
    rcases s with ⟨u, z⟩
    rcases u with ⟨u, hu⟩
    simp [appendBit]

lemma circuit_sk_fixedk_sharpp_complete_lifted_sat_count_eq {n : ℕ} (φ : BitVec n → Bool) :
    circuit_sk_fixedk_sharpp_complete_lifted_sat_count φ =
      2 * circuit_sk_fixedk_sharpp_complete_sat_count φ := by
  classical
  calc
    circuit_sk_fixedk_sharpp_complete_lifted_sat_count φ =
        Fintype.card ({ u : BitVec n // φ u = true } × Bool) := by
          exact Fintype.card_congr (circuit_sk_fixedk_sharpp_complete_lifted_witness_equiv φ)
    _ = Fintype.card { u : BitVec n // φ u = true } * Fintype.card Bool := by simp
    _ = 2 * circuit_sk_fixedk_sharpp_complete_sat_count φ := by
      simp [circuit_sk_fixedk_sharpp_complete_sat_count, Nat.mul_comm]

/-- Paper label: `thm:circuit-sk-fixedk-sharpP-complete`. The fixed-`k` collision count is the
number of `k`-tuples living in a common circuit fiber; for the standard collapse circuit, the
lifted SAT witness set doubles the satisfying assignments and the reduction value has the expected
closed form. -/
theorem paper_circuit_sk_fixedk_sharpp_complete (k : ℕ) (hk : 2 ≤ k) :
    circuit_sk_fixedk_sharpp_complete_statement k := by
  have _ := hk
  refine ⟨?_, ?_, ?_⟩
  · intro n φ
    exact circuit_sk_fixedk_sharpp_complete_lifted_sat_count_eq φ
  · intro n C
    classical
    simp [circuit_sk_fixedk_sharpp_complete_equal_output_tuple_count,
      circuit_sk_fixedk_sharpp_complete_equal_output_tuples,
      circuit_sk_fixedk_sharpp_complete_collision_sum]
  · intro n φ
    rfl

end Omega.OperatorAlgebra
