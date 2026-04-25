import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete frozen-tail data at the adjacent scales `a - 1`, `a`, and `a + 1`. -/
structure conclusion_frozen_tail_zero_curvature_second_maximum_visibility_data where
  a : ℝ
  alphaStar : ℝ
  alphaSecond : ℝ
  logPhi : ℝ
  gStar : ℝ
  pressureAtPred : ℝ
  pressureAt : ℝ
  pressureAtSucc : ℝ
  secondDifference : ℝ
  finiteScaleDelta : ℝ
  pressureAtPred_eq : pressureAtPred = (a - 1) * alphaStar + gStar
  pressureAt_eq : pressureAt = a * alphaStar + gStar
  pressureAtSucc_eq : pressureAtSucc = (a + 1) * alphaStar + gStar
  secondDifference_eq : secondDifference = pressureAtSucc - 2 * pressureAt + pressureAtPred
  finiteScaleDelta_eq :
    finiteScaleDelta = a * (alphaStar - alphaSecond) - (logPhi - gStar)

/-- Paper label: `thm:conclusion-frozen-tail-zero-curvature-second-maximum-visibility`. The three
adjacent frozen pressure samples are affine in the scale parameter, so their second finite
difference vanishes; the finite-scale delta is the recorded affine residual. -/
theorem paper_conclusion_frozen_tail_zero_curvature_second_maximum_visibility
    (D : conclusion_frozen_tail_zero_curvature_second_maximum_visibility_data) :
    D.secondDifference = 0 ∧
      D.finiteScaleDelta =
        D.a * (D.alphaStar - D.alphaSecond) - (D.logPhi - D.gStar) := by
  constructor
  · rw [D.secondDifference_eq, D.pressureAtSucc_eq, D.pressureAt_eq, D.pressureAtPred_eq]
    ring
  · exact D.finiteScaleDelta_eq

end Omega.Conclusion
