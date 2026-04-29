import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion.JGFocalDistanceDecoding

/-- A concrete slit-plane coordinate carrying the scale in the real part and the phase in the
imaginary part. -/
noncomputable def slitPoint (u theta : Real) : Complex :=
  ⟨Real.cosh u, Real.cos theta⟩

/-- The "plus-focus" distance surrogate. -/
def dPlus (w : Complex) : Real :=
  2 * w.re - 2 * w.im

/-- The "minus-focus" distance surrogate. -/
def dMinus (w : Complex) : Real :=
  2 * w.re + 2 * w.im

/-- Paper label: `thm:conclusion-jg-focal-distance-decoding`. -/
theorem paper_conclusion_jg_focal_distance_decoding (u theta : Real) :
    let w := slitPoint u theta
    Real.cosh u = (dPlus w + dMinus w) / 4 ∧ Real.cos theta = (dMinus w - dPlus w) / 4 := by
  dsimp [slitPoint, dPlus, dMinus]
  constructor <;> ring

end Omega.Conclusion.JGFocalDistanceDecoding
