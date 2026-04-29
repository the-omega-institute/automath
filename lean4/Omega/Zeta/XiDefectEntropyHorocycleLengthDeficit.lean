import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-defect-entropy-horocycle-length-deficit`. -/
theorem paper_xi_defect_entropy_horocycle_length_deficit {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    (∑ i, (m i : ℝ) * (1 - 1 / (1 + δ i))) =
        (∑ i, (m i : ℝ) * δ i / (1 + δ i)) ∧
      (∑ i, (m i : ℝ) * (1 - 1 / (1 + δ i))) =
        (∑ i, (m i : ℝ)) - ∑ i, (m i : ℝ) / (1 + δ i) := by
  constructor
  · apply Finset.sum_congr rfl
    intro i _
    have hne : 1 + δ i ≠ 0 := by linarith [hδ i]
    field_simp [hne]
    ring
  · calc
      (∑ i, (m i : ℝ) * (1 - 1 / (1 + δ i))) =
          ∑ i, ((m i : ℝ) - (m i : ℝ) / (1 + δ i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (m i : ℝ)) - ∑ i, (m i : ℝ) / (1 + δ i) := by
        rw [Finset.sum_sub_distrib]

end Omega.Zeta
