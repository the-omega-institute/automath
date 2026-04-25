import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-discriminant-degree-lowmoment-closure`. -/
theorem paper_conclusion_window6_discriminant_degree_lowmoment_closure
    (degDelta S0 S2 dimAb dimZ dimA : ℚ) (hdeg : degDelta = dimAb + S2 / 4)
    (hAb : dimAb = S0) (hZ : dimZ = S0) (hA : dimA = S2) (hS0 : S0 = 21)
    (hS2 : S2 = 212) :
    degDelta = S0 + S2 / 4 ∧ degDelta = dimZ + dimA / 4 ∧ degDelta = 74 := by
  subst dimAb
  subst dimZ
  subst dimA
  subst S0
  subst S2
  subst degDelta
  norm_num

end Omega.Conclusion
