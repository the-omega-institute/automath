import Mathlib.Tactic
import Omega.Conclusion.SoftcoreWeightMatrixExplicitInverse
import Omega.POM.ReplicaSoftcoreWordTraceFibonacciFactorization

namespace Omega.Conclusion

open Matrix

/-- The entrywise inverse-power coefficient obtained by multiplying the explicit inverse entry
against the Fibonacci bulk term from the softcore word decomposition. -/
def conclusion_softcore_inverse_power_entrywise_coefficient (q m r j : Nat) : ℚ :=
  softcoreWeightMatrixInverseEntry q r j *
    (Nat.fib (m + 1) : ℚ) ^ (q - j) *
    (Nat.fib m : ℚ) ^ j

/-- The paper-facing inverse-power package: the first-row inverse entries collapse to the two
boundary terms, the lower-triangular vanishing survives entrywise after multiplying by the
Fibonacci bulk factors, and the rank-one projector collapse contributes the Fibonacci trace term. -/
def conclusion_softcore_inverse_power_entrywise_statement (q m : Nat) : Prop :=
  conclusion_softcore_inverse_power_entrywise_coefficient q m 0 0 =
      -((Nat.fib (m + 1) : ℚ) ^ q) ∧
    conclusion_softcore_inverse_power_entrywise_coefficient q m 0 q =
      2 * (Nat.fib m : ℚ) ^ q ∧
    (∀ j : ℕ, 0 < j → j < q →
      conclusion_softcore_inverse_power_entrywise_coefficient q m 0 j = 0) ∧
    (∀ r j : ℕ, 0 < r → j < q - r →
      conclusion_softcore_inverse_power_entrywise_coefficient q m r j = 0) ∧
    Matrix.trace
        (Omega.POM.pom_replica_softcore_word_trace_fibonacci_factorization_J2 *
          Omega.Graph.goldenMeanAdjacency ^ (m - 1) *
          Omega.POM.pom_replica_softcore_word_trace_fibonacci_factorization_J2) =
      (Nat.fib m : ℤ) ∧
    Nat.fib (m + 2) = Nat.fib (m + 1) + Nat.fib m

/-- Paper label: `thm:conclusion-softcore-inverse-power-entrywise`. The explicit first-row inverse
formula gives the boundary coefficients, the remaining forbidden entries stay zero after
multiplication by the Fibonacci bulk factors, and sandwiching by the rank-one projector collapses
the word sum to the Fibonacci trace term. -/
theorem paper_conclusion_softcore_inverse_power_entrywise (q m : Nat) (hq : 2 <= q)
    (hm : 1 <= m) : conclusion_softcore_inverse_power_entrywise_statement q m := by
  have hq' : 0 < q := by omega
  rcases paper_conclusion_softcore_weight_matrix_explicit_inverse q hq' with
    ⟨h00, h0q, hmid, hvanish, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [conclusion_softcore_inverse_power_entrywise_coefficient, h00]
  · simp [conclusion_softcore_inverse_power_entrywise_coefficient, h0q]
  · intro j hj0 hjq
    simp [conclusion_softcore_inverse_power_entrywise_coefficient, hmid j hj0 hjq]
  · intro r j hr hj
    simp [conclusion_softcore_inverse_power_entrywise_coefficient, hvanish r j hr hj]
  · have htrace :=
      Omega.POM.paper_pom_replica_softcore_word_trace_fibonacci_factorization (a := m - 1) (b := 0)
    have hpred : m - 1 + 1 = m := Nat.sub_add_cancel hm
    simpa [hpred] using htrace
  · simpa [Nat.add_comm] using Nat.fib_add_two (n := m)

end Omega.Conclusion
