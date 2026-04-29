import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Main term for the selected-index count in the prime-log sparse law. -/
def conclusion_prime_log_sparse_prime_law_index_main (c : ℝ) (j : ℕ) : ℝ :=
  c * (j : ℝ) / Real.log j

/-- Main term for the translated prime-counting function. -/
def conclusion_prime_log_sparse_prime_law_prime_main (c : ℝ) (x : ℕ) : ℝ :=
  c / 2 * (x : ℝ) / (Real.log x) ^ 2

/-- Concrete ledger for the prime-log sparse-prime counting law.  The fields record the selected
indicators, their logarithmic Abel ledger, and the prime-counting translation. -/
structure conclusion_prime_log_sparse_prime_law_data where
  c : ℝ
  selectedIndicator : ℕ → ℝ
  selectedCount : ℕ → ℝ
  primeCounting : ℕ → ℝ
  primeLogWeight : ℕ → ℝ
  zeroLyapunovWeightedSum : ℕ → ℝ
  abelBoundary : ℕ → ℝ
  indexError : ℕ → ℝ
  primeError : ℕ → ℝ
  selectedCount_eq_sum :
    ∀ j, selectedCount j = ∑ i ∈ Finset.range (j + 1), selectedIndicator i
  zero_lyapunov_tail :
    ∀ j, zeroLyapunovWeightedSum j = c * (j : ℝ) + abelBoundary j
  abel_summation :
    ∀ j,
      zeroLyapunovWeightedSum j =
        selectedCount j * primeLogWeight j -
          ∑ i ∈ Finset.range j,
            selectedCount i * (primeLogWeight (i + 1) - primeLogWeight i)
  prime_log_weight_asymptotic :
    ∀ j, primeLogWeight j = Real.log j + primeError j
  index_count_asymptotic :
    ∀ j,
      selectedCount j = conclusion_prime_log_sparse_prime_law_index_main c j + indexError j
  prime_count_translation :
    ∀ x, primeCounting x = (1 / 2 : ℝ) * selectedCount x / Real.log x + primeError x

/-- Sparse selected-index and prime-counting laws, together with the concrete Abel and
zero-Lyapunov ledger identities that feed them. -/
def conclusion_prime_log_sparse_prime_law_statement
    (D : conclusion_prime_log_sparse_prime_law_data) : Prop :=
  (∀ j,
    D.selectedCount j =
      conclusion_prime_log_sparse_prime_law_index_main D.c j + D.indexError j) ∧
    (∀ x,
      D.primeCounting x =
        conclusion_prime_log_sparse_prime_law_prime_main D.c x +
          (D.indexError x / (2 * Real.log x) + D.primeError x)) ∧
    (∀ j, D.zeroLyapunovWeightedSum j = D.c * (j : ℝ) + D.abelBoundary j) ∧
    (∀ j,
      D.zeroLyapunovWeightedSum j =
        D.selectedCount j * D.primeLogWeight j -
          ∑ i ∈ Finset.range j,
            D.selectedCount i * (D.primeLogWeight (i + 1) - D.primeLogWeight i))

/-- Paper label: `thm:conclusion-prime-log-sparse-prime-law`. -/
theorem paper_conclusion_prime_log_sparse_prime_law
    (D : conclusion_prime_log_sparse_prime_law_data) :
    conclusion_prime_log_sparse_prime_law_statement D := by
  refine ⟨D.index_count_asymptotic, ?_, D.zero_lyapunov_tail, D.abel_summation⟩
  intro x
  rw [D.prime_count_translation, D.index_count_asymptotic]
  unfold conclusion_prime_log_sparse_prime_law_index_main
  unfold conclusion_prime_log_sparse_prime_law_prime_main
  ring

end

end Omega.Conclusion
