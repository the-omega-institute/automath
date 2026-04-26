namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-true-multiplicity-zeeman-impurity-splitting`. -/
theorem paper_conclusion_window6_true_multiplicity_zeeman_impurity_splitting
    (long_sector_zeeman short_sector_impurity full_operator_split : Prop)
    (hLong : long_sector_zeeman) (hShort : short_sector_impurity)
    (hAssemble : long_sector_zeeman → short_sector_impurity → full_operator_split) :
    full_operator_split := by
  exact hAssemble hLong hShort

end Omega.Conclusion
