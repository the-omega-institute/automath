import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `cor:pom-mixed-collision-pd-kernel`. Rearranging the finite sums turns the
kernel quadratic form into a sum of squares over the feature map `x ↦ (w i x)^q`. -/
theorem paper_pom_mixed_collision_pd_kernel {ι α : Type} [Fintype ι] [Fintype α] (q : ℕ)
    (w : ι → α → ℝ) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * ∑ x, (w i x) ^ q * (w j x) ^ q := by
  calc
    0 ≤ ∑ x, (∑ i, c i * (w i x) ^ q) ^ 2 := by
          exact Finset.sum_nonneg fun x _ => sq_nonneg _
    _ = ∑ i, ∑ j, c i * c j * ∑ x, (w i x) ^ q * (w j x) ^ q := by
          calc
            ∑ x, (∑ i, c i * (w i x) ^ q) ^ 2
                = ∑ x, ∑ i, ∑ j, c i * c j * ((w i x) ^ q * (w j x) ^ q) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    calc
                      (∑ i, c i * (w i x) ^ q) ^ 2
                          = (∑ i, c i * (w i x) ^ q) * (∑ j, c j * (w j x) ^ q) := by
                              rw [pow_two]
                      _ = ∑ i, (c i * (w i x) ^ q) * (∑ j, c j * (w j x) ^ q) := by
                            rw [Finset.sum_mul]
                      _ = ∑ i, ∑ j, (c i * (w i x) ^ q) * (c j * (w j x) ^ q) := by
                            refine Finset.sum_congr rfl ?_
                            intro i hi
                            rw [Finset.mul_sum]
                      _ = ∑ i, ∑ j, c i * c j * ((w i x) ^ q * (w j x) ^ q) := by
                            refine Finset.sum_congr rfl ?_
                            intro i hi
                            refine Finset.sum_congr rfl ?_
                            intro j hj
                            ring
            _ = ∑ i, ∑ x, ∑ j, c i * c j * ((w i x) ^ q * (w j x) ^ q) := by
                  rw [Finset.sum_comm]
            _ = ∑ i, ∑ j, ∑ x, c i * c j * ((w i x) ^ q * (w j x) ^ q) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  rw [Finset.sum_comm]
            _ = ∑ i, ∑ j, c i * c j * ∑ x, (w i x) ^ q * (w j x) ^ q := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  symm
                  rw [← Finset.mul_sum]

end Omega.POM
