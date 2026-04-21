import Omega.Folding.FixedFiberLedgerComplexity
import Omega.Folding.HammingDist
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

namespace Omega

open scoped BigOperators

/-- Read the distinguished Boolean coordinate from each `100/011` block. -/
def fixedFiberDecode (word : FoldFibreStarWord n) : FoldFibreStarBitstring n :=
  fun i => word i 1

/-- Clause count on the Boolean cube, viewed as the sum of satisfied positive unit clauses. -/
def fixedFiberClauseCount (w : FoldFibreStarBitstring n) : ℕ :=
  popcount w

/-- The induced objective on the distinguished fixed fiber. -/
def fixedFiberObjective (word : FoldFibreStarWord n) : ℕ :=
  fixedFiberClauseCount (fixedFiberDecode word)

/-- Maximum number of clauses affected by a single bit flip in this unit-clause model. -/
def fixedFiberClauseDegree (_n : ℕ) : ℕ :=
  1

private lemma popcount_le_popcount_add_hamming {n : ℕ} (u v : FoldFibreStarBitstring n) :
    popcount u ≤ popcount v + hammingDist u v := by
  classical
  have hsub :
      (Finset.univ.filter (fun i : Fin n => u i = true)) ⊆
        (Finset.univ.filter (fun i : Fin n => v i = true)) ∪
          (Finset.univ.filter (fun i : Fin n => u i ≠ v i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    by_cases hv : v i = true
    · exact Or.inl hv
    · right
      have hu : u i = true := hi
      simp [hu, hv]
  rw [popcount_eq_count_true, popcount_eq_count_true, hammingDist]
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

private lemma popcount_dist_le_hamming {n : ℕ} (u v : FoldFibreStarBitstring n) :
    Nat.dist (popcount u) (popcount v) ≤ hammingDist u v := by
  cases le_total (popcount u) (popcount v) with
  | inl huv =>
      rw [Nat.dist_eq_sub_of_le huv]
      have hvu : popcount v ≤ popcount u + hammingDist u v := by
        simpa [hammingDist_comm] using popcount_le_popcount_add_hamming v u
      omega
  | inr hvu =>
      rw [Nat.dist_eq_sub_of_le_right hvu]
      have huv : popcount u ≤ popcount v + hammingDist u v :=
        popcount_le_popcount_add_hamming u v
      omega

private lemma fixedFiberDecode_encode (w : FoldFibreStarBitstring n) :
    fixedFiberDecode (foldFibreStarEncode w) = w := by
  funext i
  simp [fixedFiberDecode, foldFibreStarEncode, foldFibreStarEncodeBlock]

/-- Paper label: `thm:fold-fixed-fiber-lipschitz-optimization`.
The distinguished fixed fiber is identified with the Boolean cube by the explicit block encoding,
the objective is exactly clause count on the induced assignment, and this objective is
`Δ = 1`-Lipschitz with respect to Hamming distance. -/
theorem paper_fold_fixed_fiber_lipschitz_optimization :
    (∀ n (w : FoldFibreStarBitstring n), foldFibreStarEncode w ∈ foldFibreStarFiber n) ∧
      (∀ n, Function.Injective (foldFibreStarEncode (n := n))) ∧
      (∀ n (w : FoldFibreStarBitstring n), fixedFiberDecode (foldFibreStarEncode w) = w) ∧
      (∀ n (w : FoldFibreStarBitstring n),
        fixedFiberObjective (foldFibreStarEncode w) = fixedFiberClauseCount w) ∧
      (∀ n (u v : FoldFibreStarBitstring n),
        Nat.dist (fixedFiberClauseCount u) (fixedFiberClauseCount v) ≤
          fixedFiberClauseDegree n * hammingDist u v) := by
  refine ⟨?_, foldFibreStarEncode_injective, ?_, ?_, ?_⟩
  · intro n w
    simpa [mem_foldFibreStarFiber] using foldFibreStarEncode_weight w
  · intro n w
    exact fixedFiberDecode_encode w
  · intro n w
    simp [fixedFiberObjective, fixedFiberClauseCount, fixedFiberDecode_encode]
  · intro n u v
    simpa [fixedFiberClauseCount, fixedFiberClauseDegree] using popcount_dist_le_hamming u v

end Omega
