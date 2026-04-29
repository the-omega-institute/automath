import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-window6-output-discriminant-degree-equals-conductor21-second-moment`. -/
theorem paper_conclusion_window6_output_discriminant_degree_equals_conductor21_second_moment
    (D6 M21_2 A6 C6 M1_0 M1_2 : ℚ)
    (hD : D6 = 74)
    (hM21 : M21_2 = 74)
    (hA : A6 = 21)
    (hC : C6 = 53)
    (hM10 : M1_0 = 21)
    (hM12 : M1_2 = 212) :
    D6 = M21_2 ∧ M21_2 = A6 + C6 ∧ A6 + C6 = M1_0 + M1_2 / 4 := by
  subst D6
  subst M21_2
  subst A6
  subst C6
  subst M1_0
  subst M1_2
  norm_num

end Omega.Conclusion
