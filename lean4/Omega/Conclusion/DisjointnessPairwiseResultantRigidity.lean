import Mathlib.Tactic
import Omega.Conclusion.DisjointnessPowerWordDecomposition

namespace Omega.Conclusion

/-- The mixed Fibonacci factor appearing in the audited pairwise resultant package. -/
def conclusion_disjointness_pairwise_resultant_rigidity_mixedFactor (m : ℕ) : ℕ :=
  Nat.fib (m + 2) * Nat.fib (m + 1)

/-- Node evaluation indexed by the root label `i`. -/
def conclusion_disjointness_pairwise_resultant_rigidity_nodeEvaluation (i m : ℕ) : ℕ :=
  conclusion_disjointness_pairwise_resultant_rigidity_mixedFactor m ^ i

/-- Pairwise product of the evaluations indexed by `i` and `q - i`. -/
def conclusion_disjointness_pairwise_resultant_rigidity_pairwiseResultant
    (q i m : ℕ) : ℕ :=
  conclusion_disjointness_pairwise_resultant_rigidity_nodeEvaluation i m *
    conclusion_disjointness_pairwise_resultant_rigidity_nodeEvaluation (q - i) m

/-- Paper label: `prop:conclusion-disjointness-pairwise-resultant-rigidity`.

The audited pairwise resultant is the product of the two node evaluations indexed by `i` and
`q - i`. Since both evaluations are powers of the same mixed Fibonacci factor, the paired product
collapses to a `q`-th power, and in the even case the central node specializes to the square of
the midpoint evaluation. -/
theorem paper_conclusion_disjointness_pairwise_resultant_rigidity
    (q i m : ℕ) (hi : i ≤ q) :
    conclusion_disjointness_pairwise_resultant_rigidity_pairwiseResultant q i m =
      conclusion_disjointness_pairwise_resultant_rigidity_mixedFactor m ^ q ∧
      (Even q →
        conclusion_disjointness_pairwise_resultant_rigidity_pairwiseResultant q (q / 2) m =
          (conclusion_disjointness_pairwise_resultant_rigidity_nodeEvaluation (q / 2) m) ^ 2) := by
  refine ⟨?_, ?_⟩
  · unfold conclusion_disjointness_pairwise_resultant_rigidity_pairwiseResultant
      conclusion_disjointness_pairwise_resultant_rigidity_nodeEvaluation
    rw [← pow_add, Nat.add_sub_of_le hi]
  · intro hq
    rcases hq with ⟨k, rfl⟩
    unfold conclusion_disjointness_pairwise_resultant_rigidity_pairwiseResultant
      conclusion_disjointness_pairwise_resultant_rigidity_nodeEvaluation
    have hhalf : (k + k) / 2 = k := by omega
    have hsub : k + k - k = k := by omega
    rw [hhalf, hsub]
    rw [sq]

end Omega.Conclusion
