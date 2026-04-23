import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Concrete finite data for the weak-coherence gap between the chain tree on the line metric and
its best one-chord competitor. The kernel is recorded only through the values at distances `1` and
`2`, together with the monotonicity bounds needed to dominate every non-chain competitor. -/
structure ConclusionWeakCoherenceChainTreeGapData where
  vertexCount : ℕ
  hvertexCount : 3 ≤ vertexCount
  coherenceScale : ℝ
  coherenceAmplitude : ℝ
  coherence : ℕ → ℝ
  hscale_pos : 0 < coherenceScale
  hcoherence_le_one : ∀ d : ℕ, 1 ≤ d → coherence d ≤ coherence 1
  hcoherence_le_two : ∀ d : ℕ, 2 ≤ d → coherence d ≤ coherence 2
  hcoherence_one : coherence 1 = coherenceAmplitude / coherenceScale
  hcoherence_two : coherence 2 = coherenceAmplitude / (2 * coherenceScale)

namespace ConclusionWeakCoherenceChainTreeGapData

/-- A line-metric spanning tree on `vertexCount` vertices has `vertexCount - 1` edges. -/
def conclusion_weak_coherence_chain_tree_gap_edgeCount
    (D : ConclusionWeakCoherenceChainTreeGapData) : ℕ :=
  D.vertexCount - 1

/-- The chain tree uses only unit-length edges. -/
def conclusion_weak_coherence_chain_tree_gap_chainTree
    (D : ConclusionWeakCoherenceChainTreeGapData)
    (_ : Fin D.conclusion_weak_coherence_chain_tree_gap_edgeCount) : ℕ :=
  1

/-- The best one-chord competitor replaces exactly one unit edge by a distance-`2` edge. -/
def conclusion_weak_coherence_chain_tree_gap_bestOneChordTree
    (D : ConclusionWeakCoherenceChainTreeGapData)
    (i : Fin D.conclusion_weak_coherence_chain_tree_gap_edgeCount) : ℕ :=
  if i.1 = 0 then 2 else 1

/-- Weak-coherence score of a concrete line-metric spanning tree model encoded by edge lengths. -/
def conclusion_weak_coherence_chain_tree_gap_treeCoherence
    (D : ConclusionWeakCoherenceChainTreeGapData)
    (T : Fin D.conclusion_weak_coherence_chain_tree_gap_edgeCount → ℕ) : ℝ :=
  ∑ i, D.coherence (T i)

/-- The chain coherence has `edgeCount - 1` background unit edges and one distinguished unit edge. -/
def conclusion_weak_coherence_chain_tree_gap_chainCoherence
    (D : ConclusionWeakCoherenceChainTreeGapData) : ℝ :=
  ((D.conclusion_weak_coherence_chain_tree_gap_edgeCount - 1 : ℕ) : ℝ) * D.coherence 1 +
    D.coherence 1

/-- The best non-chain competitor uses one distance-`2` edge and keeps the rest at distance `1`. -/
def conclusion_weak_coherence_chain_tree_gap_bestOneChordCoherence
    (D : ConclusionWeakCoherenceChainTreeGapData) : ℝ :=
  ((D.conclusion_weak_coherence_chain_tree_gap_edgeCount - 1 : ℕ) : ℝ) * D.coherence 1 +
    D.coherence 2

/-- A line-metric spanning tree model is the chain iff every encoded edge length equals `1`. -/
def conclusion_weak_coherence_chain_tree_gap_treeIsChain
    (D : ConclusionWeakCoherenceChainTreeGapData)
    (T : Fin D.conclusion_weak_coherence_chain_tree_gap_edgeCount → ℕ) : Prop :=
  ∀ i, T i = 1

/-- Exact finite gap statement: every non-chain tree has a distance-`2` witness, its weak-coherence
score is bounded by the one-chord competitor, and the chain/competitor gap is exactly
`κ(1) - κ(2)`. -/
def exactGapFormula (D : ConclusionWeakCoherenceChainTreeGapData) : Prop :=
  (∀ T,
      (∀ i, 1 ≤ T i) →
        ¬D.conclusion_weak_coherence_chain_tree_gap_treeIsChain T →
          ∃ i, 2 ≤ T i) ∧
    (∀ T,
      (∀ i, 1 ≤ T i) →
        (∃ i, 2 ≤ T i) →
          D.conclusion_weak_coherence_chain_tree_gap_treeCoherence T ≤
            D.conclusion_weak_coherence_chain_tree_gap_bestOneChordCoherence) ∧
    (D.conclusion_weak_coherence_chain_tree_gap_chainCoherence -
        D.conclusion_weak_coherence_chain_tree_gap_bestOneChordCoherence =
      D.coherence 1 - D.coherence 2)

/-- Specializing the weak-coherence kernel to the recorded first-order scale `A / r` yields the
explicit gap `A / (2 r)`. -/
def asymptoticSpecialization (D : ConclusionWeakCoherenceChainTreeGapData) : Prop :=
  D.conclusion_weak_coherence_chain_tree_gap_chainCoherence -
      D.conclusion_weak_coherence_chain_tree_gap_bestOneChordCoherence =
    D.coherenceAmplitude / (2 * D.coherenceScale)

end ConclusionWeakCoherenceChainTreeGapData

open ConclusionWeakCoherenceChainTreeGapData

private lemma conclusion_weak_coherence_chain_tree_gap_edgeCount_pos
    (D : ConclusionWeakCoherenceChainTreeGapData) :
    1 ≤ D.conclusion_weak_coherence_chain_tree_gap_edgeCount := by
  have hvertices : 3 ≤ D.vertexCount := D.hvertexCount
  unfold conclusion_weak_coherence_chain_tree_gap_edgeCount
  omega

private lemma conclusion_weak_coherence_chain_tree_gap_nonchain_has_long_edge
    (D : ConclusionWeakCoherenceChainTreeGapData)
    (T : Fin D.conclusion_weak_coherence_chain_tree_gap_edgeCount → ℕ)
    (hpos : ∀ i, 1 ≤ T i)
    (hnotchain : ¬D.conclusion_weak_coherence_chain_tree_gap_treeIsChain T) :
    ∃ i, 2 ≤ T i := by
  classical
  have hneq : ∃ i, T i ≠ 1 := by
    simpa [conclusion_weak_coherence_chain_tree_gap_treeIsChain, not_forall] using hnotchain
  rcases hneq with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  have hT : 1 ≤ T i := hpos i
  omega

private lemma conclusion_weak_coherence_chain_tree_gap_upper_bound
    (D : ConclusionWeakCoherenceChainTreeGapData)
    (T : Fin D.conclusion_weak_coherence_chain_tree_gap_edgeCount → ℕ)
    (hpos : ∀ i, 1 ≤ T i)
    (hwitness : ∃ i, 2 ≤ T i) :
    D.conclusion_weak_coherence_chain_tree_gap_treeCoherence T ≤
      D.conclusion_weak_coherence_chain_tree_gap_bestOneChordCoherence := by
  rcases hwitness with ⟨i, hi⟩
  have hi_mem : i ∈ (Finset.univ : Finset (Fin D.conclusion_weak_coherence_chain_tree_gap_edgeCount)) :=
    by simp
  have hsplit :
      D.conclusion_weak_coherence_chain_tree_gap_treeCoherence T =
        D.coherence (T i) +
          Finset.sum (Finset.univ.erase i) (fun j => D.coherence (T j)) := by
    unfold conclusion_weak_coherence_chain_tree_gap_treeCoherence
    simpa using
      (Finset.sum_erase_add (s := Finset.univ) (a := i) (f := fun j =>
        D.coherence (T j)) hi_mem).symm
  have hi_bound : D.coherence (T i) ≤ D.coherence 2 :=
    D.hcoherence_le_two (T i) hi
  have hrest_bound :
      Finset.sum (Finset.univ.erase i) (fun j => D.coherence (T j)) ≤
        Finset.sum (Finset.univ.erase i) (fun _j => D.coherence 1) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact D.hcoherence_le_one (T j) (hpos j)
  calc
    D.conclusion_weak_coherence_chain_tree_gap_treeCoherence T
        = D.coherence (T i) +
            Finset.sum (Finset.univ.erase i) (fun j => D.coherence (T j)) := hsplit
    _ ≤ D.coherence 2 + Finset.sum (Finset.univ.erase i) (fun _j => D.coherence 1) := by
      exact add_le_add hi_bound hrest_bound
    _ = D.conclusion_weak_coherence_chain_tree_gap_bestOneChordCoherence := by
      unfold conclusion_weak_coherence_chain_tree_gap_bestOneChordCoherence
      simp
      ring

private lemma conclusion_weak_coherence_chain_tree_gap_exact_gap
    (D : ConclusionWeakCoherenceChainTreeGapData) :
    D.conclusion_weak_coherence_chain_tree_gap_chainCoherence -
        D.conclusion_weak_coherence_chain_tree_gap_bestOneChordCoherence =
      D.coherence 1 - D.coherence 2 := by
  unfold conclusion_weak_coherence_chain_tree_gap_chainCoherence
    conclusion_weak_coherence_chain_tree_gap_bestOneChordCoherence
  ring

/-- Paper label: `thm:conclusion-weak-coherence-chain-tree-gap`. The chain tree saturates the
weak-coherence score on the line metric; every non-chain tree has at least one distance-`2` edge,
the one-chord competitor is therefore optimal among non-chain trees, and the recorded kernel scale
turns the exact finite gap into the explicit `A / (2 r)` asymptotic size. -/
theorem paper_conclusion_weak_coherence_chain_tree_gap
    (D : ConclusionWeakCoherenceChainTreeGapData) :
    D.exactGapFormula ∧ D.asymptoticSpecialization := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, conclusion_weak_coherence_chain_tree_gap_exact_gap D⟩
    · intro T hpos hnotchain
      exact conclusion_weak_coherence_chain_tree_gap_nonchain_has_long_edge D T hpos hnotchain
    · intro T hpos hwitness
      exact conclusion_weak_coherence_chain_tree_gap_upper_bound D T hpos hwitness
  · unfold ConclusionWeakCoherenceChainTreeGapData.asymptoticSpecialization
    rw [conclusion_weak_coherence_chain_tree_gap_exact_gap, D.hcoherence_one, D.hcoherence_two]
    field_simp [D.hscale_pos.ne']
    ring

end Omega.Conclusion
