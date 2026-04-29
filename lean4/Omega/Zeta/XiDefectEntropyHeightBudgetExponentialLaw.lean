import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-defect-entropy-height-budget-exponential-law`.

For a finite family of heights `s_j` with natural multiplicities `m_j`, the defect entropy
`Σ m_j (1 - exp (-s_j))` is bounded by the uniform-height value at the same weighted height
budget. This is the finite weighted Jensen inequality for the concave function
`s ↦ 1 - exp (-s)`, proved by summing its supporting tangent at the weighted mean. -/
theorem paper_xi_defect_entropy_height_budget_exponential_law {κ : ℕ}
    (m : Fin κ → ℕ) (s : Fin κ → ℝ) (hmass_pos : 0 < ∑ j, (m j : ℝ)) :
    (∑ j, (m j : ℝ) * (1 - Real.exp (-s j))) ≤
      (∑ j, (m j : ℝ)) *
        (1 - Real.exp (-((∑ j, (m j : ℝ) * s j) / (∑ j, (m j : ℝ))))) := by
  classical
  let M : ℝ := ∑ j, (m j : ℝ)
  let S : ℝ := ∑ j, (m j : ℝ) * s j
  let μ : ℝ := S / M
  have hM_ne : M ≠ 0 := ne_of_gt (by simpa [M] using hmass_pos)
  have hcenter : ∑ j, (m j : ℝ) * (s j - μ) = 0 := by
    calc
      ∑ j, (m j : ℝ) * (s j - μ) =
          ∑ j, ((m j : ℝ) * s j - μ * (m j : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
      _ = S - μ * M := by
            simp [S, M, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 0 := by
            dsimp [μ]
            field_simp [hM_ne]
            ring
  have htangent :
      ∀ j : Fin κ,
        1 - Real.exp (-s j) ≤
          (1 - Real.exp (-μ)) + Real.exp (-μ) * (s j - μ) := by
    intro j
    have hbase :
        Real.exp (-μ) * (1 + (μ - s j)) ≤ Real.exp (-s j) := by
      have hexp_linear : 1 + (μ - s j) ≤ Real.exp (μ - s j) := by
        simpa [add_comm] using Real.add_one_le_exp (μ - s j)
      have hmul :=
        mul_le_mul_of_nonneg_left hexp_linear
          (le_of_lt (Real.exp_pos (-μ)))
      calc
        Real.exp (-μ) * (1 + (μ - s j)) ≤
            Real.exp (-μ) * Real.exp (μ - s j) := hmul
        _ = Real.exp (-s j) := by
            rw [← Real.exp_add]
            ring_nf
    have hrewrite :
        Real.exp (-μ) * (1 + (μ - s j)) =
          Real.exp (-μ) - Real.exp (-μ) * (s j - μ) := by
      ring
    linarith
  have hsum :
      (∑ j, (m j : ℝ) * (1 - Real.exp (-s j))) ≤
        ∑ j,
          (m j : ℝ) *
            ((1 - Real.exp (-μ)) + Real.exp (-μ) * (s j - μ)) := by
    refine Finset.sum_le_sum ?_
    intro j _
    exact mul_le_mul_of_nonneg_left (htangent j) (by positivity)
  have hsplit :
      (∑ j,
          (m j : ℝ) *
            ((1 - Real.exp (-μ)) + Real.exp (-μ) * (s j - μ))) =
        M * (1 - Real.exp (-μ)) := by
    calc
      (∑ j,
          (m j : ℝ) *
            ((1 - Real.exp (-μ)) + Real.exp (-μ) * (s j - μ))) =
          ∑ j,
            ((m j : ℝ) * (1 - Real.exp (-μ)) +
              Real.exp (-μ) * ((m j : ℝ) * (s j - μ))) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
      _ =
          (∑ j, (m j : ℝ) * (1 - Real.exp (-μ))) +
            ∑ j, Real.exp (-μ) * ((m j : ℝ) * (s j - μ)) := by
            rw [Finset.sum_add_distrib]
      _ = M * (1 - Real.exp (-μ)) +
            Real.exp (-μ) * ∑ j, (m j : ℝ) * (s j - μ) := by
            simp [M, Finset.sum_mul, Finset.mul_sum]
      _ = M * (1 - Real.exp (-μ)) := by
            rw [hcenter, mul_zero, add_zero]
  calc
    (∑ j, (m j : ℝ) * (1 - Real.exp (-s j))) ≤
        ∑ j,
          (m j : ℝ) *
            ((1 - Real.exp (-μ)) + Real.exp (-μ) * (s j - μ)) := hsum
    _ = M * (1 - Real.exp (-μ)) := hsplit
    _ =
        (∑ j, (m j : ℝ)) *
          (1 - Real.exp (-((∑ j, (m j : ℝ) * s j) / (∑ j, (m j : ℝ))))) := by
        rfl

end Omega.Zeta
