import Mathlib

namespace Omega.Conclusion

open scoped BigOperators

/-- Beyond the shell threshold, every positive-part summand becomes affine, so the whole finite
tail sum collapses to `M * x + A`; subtracting this affine tail from `x` yields the exclusion
radius identity.
    thm:conclusion-exclusion-radius-tail-affine-recovery -/
theorem paper_conclusion_exclusion_radius_tail_affine_recovery
    (n : ℕ) (m : Fin n → ℕ) (xj : Fin n → ℝ) (xs x M A : ℝ)
    (hxs : ∀ j, xj j ≤ xs) (hx : xs ≤ x) (hM : M = ∑ j, (m j : ℝ))
    (hA : A = -∑ j, (m j : ℝ) * xj j) :
    (∑ j, (m j : ℝ) * max (x - xj j) 0 = M * x + A) ∧
      (x - ∑ j, (m j : ℝ) * max (x - xj j) 0 = (1 - M) * x - A) := by
  have hmax : ∀ j, max (x - xj j) 0 = x - xj j := by
    intro j
    apply max_eq_left
    linarith [hxs j, hx]
  have hsum :
      ∑ j, (m j : ℝ) * max (x - xj j) 0 =
        (∑ j, (m j : ℝ)) * x - ∑ j, (m j : ℝ) * xj j := by
    calc
      ∑ j, (m j : ℝ) * max (x - xj j) 0
          = ∑ j, ((m j : ℝ) * x - (m j : ℝ) * xj j) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [hmax j]
              ring
      _ = (∑ j, (m j : ℝ) * x) - ∑ j, (m j : ℝ) * xj j := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ j, (m j : ℝ)) * x - ∑ j, (m j : ℝ) * xj j := by
            congr 1
            simpa using (Finset.sum_mul (s := Finset.univ) (f := fun j : Fin n => (m j : ℝ)) x).symm
  have hA' : -∑ j, (m j : ℝ) * xj j = A := by
    simpa using hA.symm
  have htail_affine : ∑ j, (m j : ℝ) * max (x - xj j) 0 = M * x + A := by
    calc
      ∑ j, (m j : ℝ) * max (x - xj j) 0
          = (∑ j, (m j : ℝ)) * x - ∑ j, (m j : ℝ) * xj j := hsum
      _ = M * x + A := by
            rw [sub_eq_add_neg, hA', ← hM]
  constructor
  · exact htail_affine
  · calc
      x - ∑ j, (m j : ℝ) * max (x - xj j) 0 = x - (M * x + A) := by
        rw [htail_affine]
      _ = (1 - M) * x - A := by ring

end Omega.Conclusion
