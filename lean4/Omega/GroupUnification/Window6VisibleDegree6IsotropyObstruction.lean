import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.GroupUnification

/-- A visible vector contributes to the degree-6 polynomial through its three coordinates. -/
structure Window6VisibleVector where
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
deriving DecidableEq

namespace Window6VisibleVector

/-- Every visible vector in the window-6 package has at least one vanishing coordinate. -/
def HasZeroCoordinate (v : Window6VisibleVector) : Prop :=
  v.x1 = 0 ∨ v.x2 = 0 ∨ v.x3 = 0

/-- The coefficient of `x1^2 x2^2 x3^2` coming from a single degree-6 linear form. -/
def mixedDegreeSixCoefficient (v : Window6VisibleVector) : ℂ :=
  (90 : ℂ) * (v.x1 : ℂ) ^ 2 * (v.x2 : ℂ) ^ 2 * (v.x3 : ℂ) ^ 2

/-- The total pure-axis degree-6 mass contributed by a single visible vector. -/
def axisDegreeSixMass (v : Window6VisibleVector) : ℂ :=
  (v.x1 : ℂ) ^ 6 + (v.x2 : ℂ) ^ 6 + (v.x3 : ℂ) ^ 6

end Window6VisibleVector

open Window6VisibleVector
/-- Concrete degree-6 visible data. The mixed coefficient is computed termwise from the visible
support, while the axis coefficient records that the polynomial is genuinely nonzero. -/
structure Window6VisibleDegree6Data where
  support : Finset Window6VisibleVector
  weight : Window6VisibleVector → ℂ
  visible_has_zero_coordinate :
    ∀ v ∈ support, v.HasZeroCoordinate
  axisSixCoeff_ne_zero :
    (Finset.sum support fun v => weight v * v.axisDegreeSixMass) ≠ 0

namespace Window6VisibleDegree6Data

/-- The `x1^2 x2^2 x3^2` coefficient of the visible degree-6 polynomial. -/
noncomputable def coeff_x1sq_x2sq_x3sq (D : Window6VisibleDegree6Data) : ℂ :=
  Finset.sum D.support fun v => D.weight v * v.mixedDegreeSixCoefficient

/-- The sum of the pure-axis degree-6 coefficients of the visible polynomial. -/
noncomputable def axisSixCoeff (D : Window6VisibleDegree6Data) : ℂ :=
  Finset.sum D.support fun v => D.weight v * v.axisDegreeSixMass

/-- We only track the two coefficients needed for the isotropy obstruction. -/
noncomputable def poly (D : Window6VisibleDegree6Data) : ℂ × ℂ :=
  (D.coeff_x1sq_x2sq_x3sq, D.axisSixCoeff)

/-- The corresponding two coefficients of `λ (x1^2 + x2^2 + x3^2)^3`. -/
def radialSix (_D : Window6VisibleDegree6Data) (lam : ℂ) : ℂ × ℂ :=
  ((6 : ℂ) * lam, (3 : ℂ) * lam)

end Window6VisibleDegree6Data

open Window6VisibleDegree6Data

/-- `prop:window6-visible-degree6-isotropy-obstruction` -/
theorem paper_window6_visible_degree6_isotropy_obstruction (D : Window6VisibleDegree6Data) :
    D.coeff_x1sq_x2sq_x3sq = 0 ∧ ∀ lam : ℂ, D.poly ≠ D.radialSix lam := by
  have hCoeff : D.coeff_x1sq_x2sq_x3sq = 0 := by
    unfold Window6VisibleDegree6Data.coeff_x1sq_x2sq_x3sq
    refine Finset.sum_eq_zero ?_
    intro v hv
    rcases D.visible_has_zero_coordinate v hv with hx1 | hx2 | hx3
    · simp [Window6VisibleVector.mixedDegreeSixCoefficient, hx1]
    · simp [Window6VisibleVector.mixedDegreeSixCoefficient, hx2]
    · simp [Window6VisibleVector.mixedDegreeSixCoefficient, hx3]
  refine ⟨hCoeff, ?_⟩
  intro lam hEq
  have hMixed : D.coeff_x1sq_x2sq_x3sq = (6 : ℂ) * lam := congrArg Prod.fst hEq
  rw [hCoeff] at hMixed
  have hSixMul : (6 : ℂ) * lam = 0 := by simpa using hMixed.symm
  have hlam : lam = 0 := by
    exact (mul_eq_zero.mp hSixMul).resolve_left (by norm_num)
  have hAxis : D.axisSixCoeff = (3 : ℂ) * lam := congrArg Prod.snd hEq
  rw [hlam] at hAxis
  have hAxisZero : Finset.sum D.support (fun v => D.weight v * v.axisDegreeSixMass) = 0 := by
    simpa [Window6VisibleDegree6Data.axisSixCoeff] using hAxis
  exact D.axisSixCoeff_ne_zero hAxisZero

end Omega.GroupUnification
