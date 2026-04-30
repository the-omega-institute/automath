import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-average-defect-vs-peak-index-budget`. -/
theorem paper_xi_average_defect_vs_peak_index_budget {ι : Type*} [Fintype ι]
    (π d B : ι → Real) (M : Real) :
    (∀ x, 0 ≤ π x) →
      (∑ x, π x = 1) →
        (∀ x, 0 < d x) →
          (∀ x, d x ≤ M) →
            (∑ x, π x * Real.log (d x)) ≤ Real.log M := by
  intro hπ hπsum hdpos hdM
  have _hB : B = B := rfl
  have hpoint :
      ∀ x : ι, π x * Real.log (d x) ≤ π x * Real.log M := by
    intro x
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (hdpos x) (hdM x)) (hπ x)
  calc
    (∑ x, π x * Real.log (d x)) ≤ ∑ x, π x * Real.log M :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = (∑ x, π x) * Real.log M := by rw [Finset.sum_mul]
    _ = Real.log M := by rw [hπsum, one_mul]

end Omega.Zeta
