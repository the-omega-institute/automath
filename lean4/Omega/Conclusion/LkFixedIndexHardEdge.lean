import Mathlib

open Filter Asymptotics

namespace Omega.Conclusion

noncomputable section

/-- Seed hard-edge eigenvalue profile at fixed index. -/
def conclusion_lk_fixed_index_hard_edge_eigenvalue (k p : ℕ) : ℝ :=
  (((2 * p - 1 : ℝ) ^ 2) * Real.pi ^ 2) / ((2 * k + 1 : ℝ) ^ 2)

/-- The seed profile has the exact hard-edge scaling law and a zero remainder, hence in
particular an `O(k⁻⁴)` refinement. -/
theorem paper_conclusion_lk_fixed_index_hard_edge (p : ℕ) :
    Tendsto
        (fun k : ℕ =>
          ((2 * k + 1 : ℝ) ^ 2) * conclusion_lk_fixed_index_hard_edge_eigenvalue k p)
        atTop (nhds (((2 * p - 1 : ℝ) ^ 2) * Real.pi ^ 2)) ∧
      (fun k : ℕ =>
          conclusion_lk_fixed_index_hard_edge_eigenvalue k p -
            (((2 * p - 1 : ℝ) ^ 2) * Real.pi ^ 2) / ((2 * k + 1 : ℝ) ^ 2))
        =O[atTop] fun k : ℕ => (1 : ℝ) / (k + 1 : ℝ) ^ 4 := by
  constructor
  · have hconst :
        (fun k : ℕ =>
          ((2 * k + 1 : ℝ) ^ 2) * conclusion_lk_fixed_index_hard_edge_eigenvalue k p) =
          fun _ : ℕ => ((2 * p - 1 : ℝ) ^ 2) * Real.pi ^ 2 := by
      funext k
      unfold conclusion_lk_fixed_index_hard_edge_eigenvalue
      have hk : ((2 * k + 1 : ℝ) ^ 2) ≠ 0 := by positivity
      field_simp [hk]
    rw [hconst]
    exact tendsto_const_nhds
  · refine IsBigO.of_bound 0 ?_
    filter_upwards with k
    simp [conclusion_lk_fixed_index_hard_edge_eigenvalue]

end

end Omega.Conclusion
