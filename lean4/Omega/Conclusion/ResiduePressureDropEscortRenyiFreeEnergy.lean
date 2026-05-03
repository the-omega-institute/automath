import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-residue-pressure-drop-escort-renyi-free-energy`. -/
theorem paper_conclusion_residue_pressure_drop_escort_renyi_free_energy
    {ι β : Type} [Fintype ι] [Fintype β]
    (d : ι → ℝ) (dp p : ι → β → ℝ) (nu : ι → ℝ) (Sq SqP : ℝ) (q m : ℕ)
    (hd : ∀ x, d x ≠ 0) (hSq0 : Sq ≠ 0) (hSq : Sq = ∑ x, d x ^ q)
    (hSqP : SqP = ∑ x, ∑ i, dp x i ^ q) (hp : ∀ x i, p x i = dp x i / d x)
    (hnu : ∀ x, nu x = d x ^ q / Sq) :
    SqP / Sq = ∑ x, nu x * ∑ i, p x i ^ q := by
  have _ := m
  have hden : (∑ x, d x ^ q) ≠ 0 := by
    simpa [hSq] using hSq0
  calc
    SqP / Sq = (∑ x, ∑ i, dp x i ^ q) / (∑ x, d x ^ q) := by
      rw [hSqP, hSq]
    _ = ∑ x, (∑ i, dp x i ^ q) / (∑ x, d x ^ q) := by
      simp [Finset.sum_div]
    _ = ∑ x, (d x ^ q / (∑ x, d x ^ q)) * ∑ i, (dp x i / d x) ^ q := by
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [div_pow]
      field_simp [pow_ne_zero q (hd x), hden]
    _ = ∑ x, nu x * ∑ i, p x i ^ q := by
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [hnu x, hSq]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hp x i]

end Omega.Conclusion
