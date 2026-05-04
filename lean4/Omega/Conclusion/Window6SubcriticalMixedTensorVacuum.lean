import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete bidegree data for the window-`6` mixed tensor center-action obstruction. -/
structure conclusion_window6_subcritical_mixed_tensor_vacuum_Data where
  conclusion_window6_subcritical_mixed_tensor_vacuum_p : ℕ
  conclusion_window6_subcritical_mixed_tensor_vacuum_q : ℕ

namespace conclusion_window6_subcritical_mixed_tensor_vacuum_Data

/-- The absolute center weight `|q - p|` detected by the scalar action on
`(V*)^tensor p tensor V^tensor q`. -/
def centerWeight
    (D : conclusion_window6_subcritical_mixed_tensor_vacuum_Data) : ℕ :=
  if D.conclusion_window6_subcritical_mixed_tensor_vacuum_p ≤
      D.conclusion_window6_subcritical_mixed_tensor_vacuum_q then
    D.conclusion_window6_subcritical_mixed_tensor_vacuum_q -
      D.conclusion_window6_subcritical_mixed_tensor_vacuum_p
  else
    D.conclusion_window6_subcritical_mixed_tensor_vacuum_p -
      D.conclusion_window6_subcritical_mixed_tensor_vacuum_q

/-- The center acts trivially only when the window-`6` dimension divides the mixed tensor weight. -/
def centerActionAllows
    (D : conclusion_window6_subcritical_mixed_tensor_vacuum_Data) : Prop :=
  21 ∣ D.centerWeight

/-- In total tensor degree below `21`, an unbalanced mixed tensor has no center-compatible
invariant channel. -/
def mixedTensorVacuum
    (D : conclusion_window6_subcritical_mixed_tensor_vacuum_Data) : Prop :=
  D.conclusion_window6_subcritical_mixed_tensor_vacuum_p +
      D.conclusion_window6_subcritical_mixed_tensor_vacuum_q < 21 →
    D.conclusion_window6_subcritical_mixed_tensor_vacuum_p ≠
      D.conclusion_window6_subcritical_mixed_tensor_vacuum_q →
      ¬ D.centerActionAllows

end conclusion_window6_subcritical_mixed_tensor_vacuum_Data

/-- Paper label: `thm:conclusion-window6-subcritical-mixed-tensor-vacuum`. -/
theorem paper_conclusion_window6_subcritical_mixed_tensor_vacuum
    (D : conclusion_window6_subcritical_mixed_tensor_vacuum_Data) :
    D.mixedTensorVacuum := by
  intro hsub hneq hcenter
  rw [conclusion_window6_subcritical_mixed_tensor_vacuum_Data.centerActionAllows,
    conclusion_window6_subcritical_mixed_tensor_vacuum_Data.centerWeight] at hcenter
  by_cases hpq :
      D.conclusion_window6_subcritical_mixed_tensor_vacuum_p ≤
        D.conclusion_window6_subcritical_mixed_tensor_vacuum_q
  · simp [hpq] at hcenter
    have hdiff_lt :
        D.conclusion_window6_subcritical_mixed_tensor_vacuum_q -
            D.conclusion_window6_subcritical_mixed_tensor_vacuum_p < 21 := by
      omega
    have hdiff_pos :
        0 <
          D.conclusion_window6_subcritical_mixed_tensor_vacuum_q -
            D.conclusion_window6_subcritical_mixed_tensor_vacuum_p := by
      omega
    exact (Nat.not_le_of_gt hdiff_lt) (Nat.le_of_dvd hdiff_pos hcenter)
  · simp [hpq] at hcenter
    have hdiff_lt :
        D.conclusion_window6_subcritical_mixed_tensor_vacuum_p -
            D.conclusion_window6_subcritical_mixed_tensor_vacuum_q < 21 := by
      omega
    have hdiff_pos :
        0 <
          D.conclusion_window6_subcritical_mixed_tensor_vacuum_p -
            D.conclusion_window6_subcritical_mixed_tensor_vacuum_q := by
      omega
    exact (Nat.not_le_of_gt hdiff_lt) (Nat.le_of_dvd hdiff_pos hcenter)

end Omega.Conclusion
