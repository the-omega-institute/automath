import Mathlib

open scoped BigOperators

namespace Omega.HighDimensionalCutProject.IndicatorSumRewrite

theorem paper_high_dimensional_cut_project_indicator_sum_rewrite_seeds
    {n : ℕ} (f : Fin n → ℝ) (S : Finset (Fin n)) :
    ∑ i ∈ S, f i = ∑ i ∈ Finset.univ, if i ∈ S then f i else 0 := by
  rw [Finset.sum_ite_mem]
  simp

theorem paper_high_dimensional_cut_project_indicator_sum_rewrite_package
    {n : ℕ} (f : Fin n → ℝ) (S : Finset (Fin n)) :
    ∑ i ∈ S, f i = ∑ i ∈ Finset.univ, if i ∈ S then f i else 0 :=
  paper_high_dimensional_cut_project_indicator_sum_rewrite_seeds f S

theorem paper_high_dimensional_cut_project_indicator_sum_rewrite
    {n : ℕ} (f : Fin n → ℝ) (S : Finset (Fin n)) :
    ∑ i ∈ S, f i = ∑ i ∈ Finset.univ, if i ∈ S then f i else 0 := by
  exact paper_high_dimensional_cut_project_indicator_sum_rewrite_package f S

end Omega.HighDimensionalCutProject.IndicatorSumRewrite
