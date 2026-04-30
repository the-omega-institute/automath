namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-rh-from-uniform-l2-stability`. -/
theorem paper_conclusion_rh_from_uniform_l2_stability
    (RH uniformL2Stability uniformComovingDefect : Prop)
    (hL2_to_defect : uniformL2Stability → uniformComovingDefect)
    (hDefect_to_RH : uniformComovingDefect → RH) :
    uniformL2Stability → RH := by
  intro hL2
  exact hDefect_to_RH (hL2_to_defect hL2)

end Omega.Conclusion
