import Omega.OperatorAlgebra.FoldCapacityCurveCompleteInvariant

namespace Omega.OperatorAlgebra

/-- Positive slope-jump locations of the discrete capacity curve. -/
def foldCapacityKinkSet (degrees : Finset ℕ) : Finset ℕ :=
  degrees.filter fun t => t ≠ 0 ∧ 0 < foldTailCount degrees t - foldTailCount degrees (t + 1)

private lemma foldMultiplicityCount_eq_one_of_mem {degrees : Finset ℕ} {t : ℕ} (ht : t ∈ degrees) :
    foldMultiplicityCount degrees t = 1 := by
  classical
  unfold foldMultiplicityCount
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hbt
    simp [hbt]
  · intro hnot
    exact (hnot ht).elim

/-- Paper label: `prop:op-algebra-capacity-kinks-equal-spectrum-levels`.

For the finitary capacity-curve model, the positive kink set is exactly the set of positive degree
levels, so the number of kinks equals the number of distinct positive spectrum values. -/
theorem paper_op_algebra_capacity_kinks_equal_spectrum_levels (degrees : Finset ℕ) :
    foldCapacityKinkSet degrees = degrees.erase 0 ∧
      (foldCapacityKinkSet degrees).card = (degrees.erase 0).card := by
  have hkset : foldCapacityKinkSet degrees = degrees.erase 0 := by
    ext t
    constructor
    · intro ht
      rcases Finset.mem_filter.mp ht with ⟨htdeg, hpred⟩
      exact Finset.mem_erase.mpr ⟨hpred.1, htdeg⟩
    · intro ht
      rcases Finset.mem_erase.mp ht with ⟨hne, htdeg⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨htdeg, hne, ?_⟩
      rw [← foldMultiplicityCount_eq_tail_sub degrees t]
      simpa [foldMultiplicityCount_eq_one_of_mem htdeg]
  constructor
  · exact hkset
  · simpa [hkset]

end Omega.OperatorAlgebra
