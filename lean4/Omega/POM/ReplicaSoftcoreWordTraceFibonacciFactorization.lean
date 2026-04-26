import Mathlib.Tactic
import Omega.Graph.TransferMatrix

namespace Omega.POM

open Matrix

/-- The rank-one `J2 = u uᵀ` projector selecting the `0`-coordinate line in the concrete
replica-softcore two-state model. -/
def pom_replica_softcore_word_trace_fibonacci_factorization_J2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, 0]

/-- Left multiplication by `J2` keeps only the first row. -/
lemma pom_replica_softcore_word_trace_fibonacci_factorization_left (n : ℕ) :
    pom_replica_softcore_word_trace_fibonacci_factorization_J2 *
        Omega.Graph.goldenMeanAdjacency ^ n =
      !![(Omega.Graph.goldenMeanAdjacency ^ n) 0 0,
        (Omega.Graph.goldenMeanAdjacency ^ n) 0 1;
        0, 0] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pom_replica_softcore_word_trace_fibonacci_factorization_J2, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Sandwiching a Fibonacci transfer block by `J2` keeps only the `(0,0)` entry, which is the
Fibonacci number `F_{n+1}`. -/
lemma pom_replica_softcore_word_trace_fibonacci_factorization_sandwich (n : ℕ) :
    pom_replica_softcore_word_trace_fibonacci_factorization_J2 *
        Omega.Graph.goldenMeanAdjacency ^ n *
        pom_replica_softcore_word_trace_fibonacci_factorization_J2 =
      !![(Nat.fib (n + 1) : ℤ), 0; 0, 0] := by
  rw [pom_replica_softcore_word_trace_fibonacci_factorization_left]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pom_replica_softcore_word_trace_fibonacci_factorization_J2, Matrix.mul_apply,
      Fin.sum_univ_two, Omega.Graph.goldenMeanAdjacency_pow_00]

/-- Paper label: `prop:pom-replica-softcore-word-trace-fibonacci-factorization`. Any concrete word
containing a `J2` block factors through the Fibonacci `(0,0)` transfer-matrix entries. -/
def pom_replica_softcore_word_trace_fibonacci_factorization_statement : Prop :=
  ∀ a b : ℕ,
    Matrix.trace
        (pom_replica_softcore_word_trace_fibonacci_factorization_J2 *
          Omega.Graph.goldenMeanAdjacency ^ a *
          pom_replica_softcore_word_trace_fibonacci_factorization_J2 *
          Omega.Graph.goldenMeanAdjacency ^ b) =
      (Nat.fib (a + 1) * Nat.fib (b + 1) : ℤ)

theorem paper_pom_replica_softcore_word_trace_fibonacci_factorization :
    pom_replica_softcore_word_trace_fibonacci_factorization_statement := by
  intro a b
  have hrewrite :
      pom_replica_softcore_word_trace_fibonacci_factorization_J2 *
          Omega.Graph.goldenMeanAdjacency ^ a *
          pom_replica_softcore_word_trace_fibonacci_factorization_J2 *
          Omega.Graph.goldenMeanAdjacency ^ b =
        (!![(Nat.fib (a + 1) : ℤ), 0; 0, 0]) * Omega.Graph.goldenMeanAdjacency ^ b := by
    simpa [Matrix.mul_assoc] using
      congrArg
        (fun M => M * Omega.Graph.goldenMeanAdjacency ^ b)
        (pom_replica_softcore_word_trace_fibonacci_factorization_sandwich a)
  rw [hrewrite]
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Omega.Graph.goldenMeanAdjacency_pow_00]

end Omega.POM
