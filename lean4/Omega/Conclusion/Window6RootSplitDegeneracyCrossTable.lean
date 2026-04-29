import Mathlib.Tactic

namespace Omega.Conclusion

/-- Boundary-sector bin-fold degeneracies in the window-`6` cross table. -/
def conclusion_window6_root_split_degeneracy_cross_table_boundaryDegeneracies : List ℕ :=
  [2, 2, 2]

/-- Cyclic-sector bin-fold degeneracies in the window-`6` cross table. -/
def conclusion_window6_root_split_degeneracy_cross_table_cyclicDegeneracies : List ℕ :=
  [2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4]

/-- Count the entries in a finite degeneracy stratum. -/
def conclusion_window6_root_split_degeneracy_cross_table_count
    (xs : List ℕ) (r : ℕ) : ℕ :=
  (xs.filter fun d => d = r).length

/-- Concrete six-entry window-`6` root-split/bin-fold cross table. -/
def conclusion_window6_root_split_degeneracy_cross_table_statement : Prop :=
  conclusion_window6_root_split_degeneracy_cross_table_count
      conclusion_window6_root_split_degeneracy_cross_table_boundaryDegeneracies 2 = 3 ∧
    conclusion_window6_root_split_degeneracy_cross_table_count
      conclusion_window6_root_split_degeneracy_cross_table_boundaryDegeneracies 3 = 0 ∧
    conclusion_window6_root_split_degeneracy_cross_table_count
      conclusion_window6_root_split_degeneracy_cross_table_boundaryDegeneracies 4 = 0 ∧
    conclusion_window6_root_split_degeneracy_cross_table_count
      conclusion_window6_root_split_degeneracy_cross_table_cyclicDegeneracies 2 = 5 ∧
    conclusion_window6_root_split_degeneracy_cross_table_count
      conclusion_window6_root_split_degeneracy_cross_table_cyclicDegeneracies 3 = 4 ∧
    conclusion_window6_root_split_degeneracy_cross_table_count
      conclusion_window6_root_split_degeneracy_cross_table_cyclicDegeneracies 4 = 9

/-- Paper label: `cor:conclusion-window6-root-split-degeneracy-cross-table`. -/
theorem paper_conclusion_window6_root_split_degeneracy_cross_table :
    conclusion_window6_root_split_degeneracy_cross_table_statement := by
  unfold conclusion_window6_root_split_degeneracy_cross_table_statement
  unfold conclusion_window6_root_split_degeneracy_cross_table_count
  unfold conclusion_window6_root_split_degeneracy_cross_table_boundaryDegeneracies
  unfold conclusion_window6_root_split_degeneracy_cross_table_cyclicDegeneracies
  norm_num

end Omega.Conclusion
