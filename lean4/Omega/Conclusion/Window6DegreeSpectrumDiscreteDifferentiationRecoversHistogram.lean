import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-window6-degree-spectrum-discrete-differentiation-recovers-histogram`. -/
theorem paper_conclusion_window6_degree_spectrum_discrete_differentiation_recovers_histogram
    (g2 g3 g4 : ℕ) (hg2 : g2 = 21) (hg3 : g3 = 13) (hg4 : g4 = 9) :
    g2 - g3 = 8 ∧ g3 - g4 = 4 ∧ g4 = 9 := by
  subst g2
  subst g3
  subst g4
  norm_num

end Omega.Conclusion
