import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.Graph.TransferMatrix

namespace Omega.POM

open Matrix

/-- The all-ones rank-one block `J₂` from the replica-softcore word expansion. -/
def pom_replica_softcore_word_trace_power_sums_J2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 1, 1]

/-- The Fibonacci transfer block `K`. -/
abbrev pom_replica_softcore_word_trace_power_sums_K : Matrix (Fin 2) (Fin 2) ℤ :=
  Omega.Graph.goldenMeanAdjacency

/-- The pure `K^m` term left after removing the determinant-zero `J₂` words. -/
def pom_replica_softcore_word_trace_power_sums_pureKTerm (q m : ℕ) : ℤ :=
  (Matrix.trace (pom_replica_softcore_word_trace_power_sums_K ^ m)) ^ q

/-- Concrete collapse package for the word-trace power-sum argument: the `J₂`-containing blocks
all have determinant `0`, so their full-trace and exceptional-trace contributions coincide, while
the pure `K^m` block contributes exactly the leftover term. -/
def pom_replica_softcore_word_trace_power_sums_statement (q m : ℕ) : Prop :=
  Matrix.det pom_replica_softcore_word_trace_power_sums_J2 = 0 ∧
    Matrix.det
        (pom_replica_softcore_word_trace_power_sums_K ^ m *
          pom_replica_softcore_word_trace_power_sums_J2) = 0 ∧
    Matrix.det
        (pom_replica_softcore_word_trace_power_sums_J2 *
          pom_replica_softcore_word_trace_power_sums_K ^ m) = 0 ∧
    (if Matrix.det
          (pom_replica_softcore_word_trace_power_sums_K ^ m *
            pom_replica_softcore_word_trace_power_sums_J2) =
          0 then
        (Matrix.trace
            (pom_replica_softcore_word_trace_power_sums_K ^ m *
              pom_replica_softcore_word_trace_power_sums_J2)) ^ q
      else
        0) =
      (Matrix.trace
          (pom_replica_softcore_word_trace_power_sums_K ^ m *
            pom_replica_softcore_word_trace_power_sums_J2)) ^ q ∧
    (if Matrix.det
          (pom_replica_softcore_word_trace_power_sums_J2 *
            pom_replica_softcore_word_trace_power_sums_K ^ m) =
          0 then
        (Matrix.trace
            (pom_replica_softcore_word_trace_power_sums_J2 *
              pom_replica_softcore_word_trace_power_sums_K ^ m)) ^ q
      else
        0) =
      (Matrix.trace
          (pom_replica_softcore_word_trace_power_sums_J2 *
            pom_replica_softcore_word_trace_power_sums_K ^ m)) ^ q ∧
    (Matrix.trace (pom_replica_softcore_word_trace_power_sums_K ^ m)) ^ q =
      (if Matrix.det (pom_replica_softcore_word_trace_power_sums_K ^ m) = 0 then
        (Matrix.trace (pom_replica_softcore_word_trace_power_sums_K ^ m)) ^ q
      else
        0) +
        pom_replica_softcore_word_trace_power_sums_pureKTerm q m

lemma pom_replica_softcore_word_trace_power_sums_det_J2 :
    Matrix.det pom_replica_softcore_word_trace_power_sums_J2 = 0 := by
  norm_num [pom_replica_softcore_word_trace_power_sums_J2, Matrix.det_fin_two]

lemma pom_replica_softcore_word_trace_power_sums_det_K :
    Matrix.det pom_replica_softcore_word_trace_power_sums_K = -1 := by
  norm_num [pom_replica_softcore_word_trace_power_sums_K, Omega.Graph.goldenMeanAdjacency,
    Matrix.det_fin_two]

lemma pom_replica_softcore_word_trace_power_sums_det_K_pow_ne_zero (m : ℕ) :
    Matrix.det (pom_replica_softcore_word_trace_power_sums_K ^ m) ≠ 0 := by
  simp [Matrix.det_pow, pom_replica_softcore_word_trace_power_sums_det_K]

lemma pom_replica_softcore_word_trace_power_sums_proof (q m : ℕ) :
    pom_replica_softcore_word_trace_power_sums_statement q m := by
  have hdetJ2 := pom_replica_softcore_word_trace_power_sums_det_J2
  have hdetRight :
      Matrix.det
          (pom_replica_softcore_word_trace_power_sums_K ^ m *
            pom_replica_softcore_word_trace_power_sums_J2) = 0 := by
    simp [Matrix.det_mul, hdetJ2]
  have hdetLeft :
      Matrix.det
          (pom_replica_softcore_word_trace_power_sums_J2 *
            pom_replica_softcore_word_trace_power_sums_K ^ m) = 0 := by
    simp [Matrix.det_mul, hdetJ2]
  have hdetPure :
      Matrix.det (pom_replica_softcore_word_trace_power_sums_K ^ m) ≠ 0 :=
    pom_replica_softcore_word_trace_power_sums_det_K_pow_ne_zero m
  refine ⟨hdetJ2, hdetRight, hdetLeft, ?_, ?_, ?_⟩
  · simp [hdetRight]
  · simp [hdetLeft]
  · rw [if_neg hdetPure]
    simp [pom_replica_softcore_word_trace_power_sums_pureKTerm]

/-- Paper label: `thm:pom-replica-softcore-word-trace-power-sums`. -/
theorem paper_pom_replica_softcore_word_trace_power_sums (q m : ℕ) :
    pom_replica_softcore_word_trace_power_sums_statement q m :=
  pom_replica_softcore_word_trace_power_sums_proof q m

end Omega.POM
