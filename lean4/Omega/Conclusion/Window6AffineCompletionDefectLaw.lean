import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `prop:conclusion-window6-affine-completion-defect-law`. -/
theorem paper_conclusion_window6_affine_completion_defect_law
    (R4skew R3punc : Finset (Fin 21)) (Delta : Fin 21 → ℕ)
    (hdisj : Disjoint R4skew R3punc)
    (hR4 : R4skew.card = 6)
    (hR3 : R3punc.card = 4)
    (hDelta : ∀ r, Delta r = if r ∈ R4skew then 4 else if r ∈ R3punc then 1 else 0) :
    ((∑ r : Fin 21, Delta r) = 28) ∧
      (R4skew.sum Delta = 24) ∧
      (R3punc.sum Delta = 4) := by
  classical
  have hR4sum : R4skew.sum Delta = 24 := by
    calc
      R4skew.sum Delta = R4skew.sum (fun _r => (4 : ℕ)) := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        simp [hDelta r, hr]
      _ = 24 := by
        simp [hR4]
  have hR3sum : R3punc.sum Delta = 4 := by
    calc
      R3punc.sum Delta = R3punc.sum (fun _r => (1 : ℕ)) := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        have hnR4 : r ∉ R4skew := by
          intro hR4mem
          exact (Finset.disjoint_left.mp hdisj hR4mem hr)
        simp [hDelta r, hnR4, hr]
      _ = 4 := by
        simp [hR3]
  have htotalSupport :
      (∑ r : Fin 21, Delta r) = (R4skew ∪ R3punc).sum Delta := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro r _hr
      simp
    · intro r _hr hnot
      have hnR4 : r ∉ R4skew := by
        intro hr
        exact hnot (by simp [hr])
      have hnR3 : r ∉ R3punc := by
        intro hr
        exact hnot (by simp [hr])
      simp [hDelta r, hnR4, hnR3]
  have hunion :
      (R4skew ∪ R3punc).sum Delta = R4skew.sum Delta + R3punc.sum Delta := by
    exact Finset.sum_union hdisj
  have htot : (∑ r : Fin 21, Delta r) = 28 := by
    rw [htotalSupport, hunion]
    rw [hR4sum, hR3sum]
  exact ⟨htot, hR4sum, hR3sum⟩

end Omega.Conclusion
