import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-microcanonical-query-distortion-critical-window-variance-psi`. -/
theorem paper_pom_microcanonical_query_distortion_critical_window_variance_psi {ι : Type*}
    [Fintype ι] (β : ℝ) (w ψ : ι → ℝ) (hw_sum : (∑ x, w x) = 1) :
    β * (1 - β) * (∑ x, w x * (2 * ψ x - ∑ y, w y * (2 * ψ y)) ^ 2) =
      4 * β * (1 - β) * ((∑ x, w x * ψ x ^ 2) - (∑ x, w x * ψ x) ^ 2) := by
  classical
  have hcenter :
      (∑ x, w x * (2 * ψ x - ∑ y, w y * (2 * ψ y)) ^ 2) =
        4 * ((∑ x, w x * ψ x ^ 2) - (∑ x, w x * ψ x) ^ 2) := by
    rw [show (∑ y, w y * (2 * ψ y)) = 2 * ∑ y, w y * ψ y by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro y _
      ring]
    rw [show (∑ x, w x * (2 * ψ x - 2 * ∑ y, w y * ψ y) ^ 2) =
        ∑ x, (4 * (w x * ψ x ^ 2) -
          8 * ((∑ y, w y * ψ y) * (w x * ψ x)) +
          4 * ((∑ y, w y * ψ y) ^ 2 * w x)) by
      refine Finset.sum_congr rfl ?_
      intro x _
      ring]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring_nf
    set A : ℝ := ∑ x, w x * ψ x with hA
    set B : ℝ := ∑ x, w x * ψ x ^ 2 with hB
    have h1 : (∑ x, w x * ψ x ^ 2 * 4) = B * 4 := by
      rw [show (∑ x, w x * ψ x ^ 2 * 4) = (∑ x, w x * ψ x ^ 2) * 4 by
        rw [← Finset.sum_mul]]
    have h2 : (∑ x, A * w x * ψ x * 8) = A * A * 8 := by
      calc
        (∑ x, A * w x * ψ x * 8) = ∑ x, (w x * ψ x) * (A * 8) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
        _ = (∑ x, w x * ψ x) * (A * 8) := by
          rw [← Finset.sum_mul]
        _ = A * A * 8 := by
          rw [← hA]
          ring
    have h3 : (∑ x, A ^ 2 * w x * 4) = A ^ 2 * 4 := by
      calc
        (∑ x, A ^ 2 * w x * 4) = ∑ x, w x * (A ^ 2 * 4) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
        _ = (∑ x, w x) * (A ^ 2 * 4) := by
          rw [← Finset.sum_mul]
        _ = A ^ 2 * 4 := by
          rw [hw_sum]
          ring
    rw [h1, h2, h3]
    ring
  rw [hcenter]
  ring

end Omega.POM
