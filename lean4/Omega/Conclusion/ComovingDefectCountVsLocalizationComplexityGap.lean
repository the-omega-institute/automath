import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete scalar data for the comoving defect-count versus localization
complexity gap.  The sandwich bounds and finite-prefix recovery requirement are
kept as inequalities over natural-indexed quantities. -/
structure conclusion_comoving_defect_count_vs_localization_complexity_gap_data where
  defectCount : ℕ → ℝ
  l1Lower : ℕ → ℝ
  linftyUpper : ℕ → ℝ
  prefixLength : ℕ → ℕ
  defect_count_lower : ∀ m : ℕ, l1Lower m ≤ defectCount m
  defect_count_upper : ∀ m : ℕ, defectCount m ≤ linftyUpper m
  prony_prefix_requirement : ∀ κ : ℕ, 2 * κ ≤ prefixLength κ

/-- The `L¹`/`L∞` scalar sandwich on the comoving defect count. -/
def conclusion_comoving_defect_count_vs_localization_complexity_gap_data.defect_count_bounds
    (D : conclusion_comoving_defect_count_vs_localization_complexity_gap_data) :
    Prop :=
  ∀ m : ℕ, D.l1Lower m ≤ D.defectCount m ∧ D.defectCount m ≤ D.linftyUpper m

/-- Prony-style finite-prefix recovery requires a prefix of length at least
`2κ` for a localization problem with `κ` defects. -/
def conclusion_comoving_defect_count_vs_localization_complexity_gap_data.localization_requires_prefix_length
    (D : conclusion_comoving_defect_count_vs_localization_complexity_gap_data) :
    Prop :=
  ∀ κ : ℕ, 2 * κ ≤ D.prefixLength κ

/-- thm:conclusion-comoving-defect-count-vs-localization-complexity-gap -/
theorem paper_conclusion_comoving_defect_count_vs_localization_complexity_gap
    (D : conclusion_comoving_defect_count_vs_localization_complexity_gap_data) :
    D.defect_count_bounds ∧ D.localization_requires_prefix_length := by
  refine ⟨?_, ?_⟩
  · intro m
    exact ⟨D.defect_count_lower m, D.defect_count_upper m⟩
  · intro κ
    exact D.prony_prefix_requirement κ

end Omega.Conclusion
