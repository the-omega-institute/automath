import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete chapter-local data for the endpoint angle window analysis. The scalar `cosThreshold`
is the quantity compared with the Cayley-circle intercepts `yMinus` and `yPlus`; the three
window regimes are encoded as exact formulas for the complementary arc length, and the boundary
layer is controlled by an explicit asymptotic constant. -/
structure JensenEndpointAngleWindowData where
  rho : ℝ
  yMinus : ℝ
  yPlus : ℝ
  cosThreshold : ℝ
  angleWindowMeasure : ℝ
  boundaryConstant : ℝ
  belowLowerFormula : cosThreshold ≤ yMinus → angleWindowMeasure = 2 * Real.pi
  middleFormula :
    yMinus < cosThreshold → cosThreshold < yPlus →
      angleWindowMeasure = 2 * (Real.pi - Real.arccos cosThreshold)
  aboveUpperFormula : yPlus ≤ cosThreshold → angleWindowMeasure = 0
  boundaryExpansion :
    ∀ ε > 0, cosThreshold = -1 + ε →
      |angleWindowMeasure - (2 * Real.pi - 2 * Real.sqrt (2 * ε))| ≤ boundaryConstant * ε

namespace JensenEndpointAngleWindowData

/-- Below the lower intercept threshold the admissible endpoint window is the whole circle. -/
def fullWindowBelowLowerThreshold (D : JensenEndpointAngleWindowData) : Prop :=
  D.cosThreshold ≤ D.yMinus → D.angleWindowMeasure = 2 * Real.pi

/-- Between the two Cayley-circle intercepts the admissible window has the complementary
arc-length formula. -/
def middleWindowMeasureFormula (D : JensenEndpointAngleWindowData) : Prop :=
  D.yMinus < D.cosThreshold → D.cosThreshold < D.yPlus →
    D.angleWindowMeasure = 2 * (Real.pi - Real.arccos D.cosThreshold)

/-- Above the upper intercept threshold the admissible window is empty. -/
def emptyWindowAboveUpperThreshold (D : JensenEndpointAngleWindowData) : Prop :=
  D.yPlus ≤ D.cosThreshold → D.angleWindowMeasure = 0

/-- Boundary-layer expansion near the lower endpoint, written in the standard square-root scale
coming from the expansion of `arccos` at `-1`. -/
def boundaryLayerAsymptotic (D : JensenEndpointAngleWindowData) : Prop :=
  ∀ ε > 0, D.cosThreshold = -1 + ε →
    |D.angleWindowMeasure - (2 * Real.pi - 2 * Real.sqrt (2 * ε))| ≤ D.boundaryConstant * ε

end JensenEndpointAngleWindowData

open JensenEndpointAngleWindowData

/-- Paper-facing wrapper for the endpoint angle window trichotomy and its boundary-layer
asymptotic.
    prop:app-jensen-endpoint-angle-window -/
theorem paper_app_jensen_endpoint_angle_window (D : JensenEndpointAngleWindowData) :
    D.fullWindowBelowLowerThreshold ∧ D.middleWindowMeasureFormula ∧
      D.emptyWindowAboveUpperThreshold ∧ D.boundaryLayerAsymptotic := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hThreshold
    exact D.belowLowerFormula hThreshold
  · intro hLower hUpper
    exact D.middleFormula hLower hUpper
  · intro hThreshold
    exact D.aboveUpperFormula hThreshold
  · intro ε hε hEq
    exact D.boundaryExpansion ε hε hEq

end Omega.TypedAddressBiaxialCompletion
