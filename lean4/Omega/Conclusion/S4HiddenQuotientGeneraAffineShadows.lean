import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-s4-hidden-quotient-genera-affine-shadows`. -/
theorem paper_conclusion_s4_hidden_quotient_genera_affine_shadows
    (gH gZ gCF dimP gC2 gC3 : Nat)
    (hH : gH = 5)
    (hZ : gZ = 4)
    (hCF : gCF = 3)
    (hP : dimP = 9)
    (hC2 : gC2 = 2 * gCF + gZ + dimP)
    (hC3 : gC3 = gH + gCF + dimP) :
    gC2 = 19 ∧ gC3 = 17 := by
  constructor
  · simp [hC2, hCF, hZ, hP]
  · simp [hC3, hH, hCF, hP]

end Omega.Conclusion
