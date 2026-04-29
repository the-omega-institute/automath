import Mathlib.Tactic

namespace Omega.Zeta

/-- The cubic defining the affine model `u^2 = f(m)` for the `E_D` fiber. -/
def xiEdInftyFiberCubic (m : ℚ) : ℚ :=
  -4 * m ^ 3 - 16 * m ^ 2 + 16 * m + 65

/-- The affine `E_D` model used in the `\infty`-fiber calculation. -/
def xiEdInftyFiberOnCurve (m u : ℚ) : Prop :=
  u ^ 2 = xiEdInftyFiberCubic m

/-- The tangent-slope formula coming from implicit differentiation of `u^2 = f(m)`. -/
def xiEdInftyFiberFormalSlope (m u : ℚ) : ℚ :=
  (-12 * m ^ 2 - 32 * m + 16) / (2 * u)

/-- The tangent line through `Q₁ = (-8,-31)`. -/
def xiEdInftyFiberTangentLine (m : ℚ) : ℚ :=
  8 * m + 33

/-- Concrete package for the halving point `Q₁`, its tangent slope, and the tangent factorization
used to identify the residual intersection point. -/
structure XiEdInftyFiberHalvingTangentIntegralPackage where
  q1OnCurve : xiEdInftyFiberOnCurve (-8) (-31)
  tangentSlopeAtQ1 : xiEdInftyFiberFormalSlope (-8) (-31) = 8
  tangentLineAtQ1 : xiEdInftyFiberTangentLine (-8) = -31
  tangentLineClosedForm : ∀ m : ℚ, xiEdInftyFiberTangentLine m = 8 * m + 33
  tangentFactorization :
    ∀ m : ℚ,
      xiEdInftyFiberCubic m - (xiEdInftyFiberTangentLine m) ^ 2 =
        -4 * (m + 4) * (m + 8) ^ 2
  residualIntersection : xiEdInftyFiberOnCurve (-4) 1
  reflectedResidual : xiEdInftyFiberOnCurve (-4) (-1)

/-- `prop:xi-ed-infty-fiber-halving-tangent-integral`. The point `Q₁ = (-8,-31)` lies on
`u^2 = -4m^3 - 16m^2 + 16m + 65`, its tangent has slope `8` and equation `u = 8m + 33`, and the
resulting substitution factors as `-4 (m + 4) (m + 8)^2`, leaving the residual point `(-4,1)` and
its reflection `(-4,-1)`. -/
theorem paper_xi_ed_infty_fiber_halving_tangent_integral :
    XiEdInftyFiberHalvingTangentIntegralPackage := by
  refine
    { q1OnCurve := ?_
      tangentSlopeAtQ1 := ?_
      tangentLineAtQ1 := ?_
      tangentLineClosedForm := ?_
      tangentFactorization := ?_
      residualIntersection := ?_
      reflectedResidual := ?_ }
  · norm_num [xiEdInftyFiberOnCurve, xiEdInftyFiberCubic]
  · norm_num [xiEdInftyFiberFormalSlope]
  · norm_num [xiEdInftyFiberTangentLine]
  · intro m
    rfl
  · intro m
    unfold xiEdInftyFiberCubic xiEdInftyFiberTangentLine
    ring
  · norm_num [xiEdInftyFiberOnCurve, xiEdInftyFiberCubic]
  · norm_num [xiEdInftyFiberOnCurve, xiEdInftyFiberCubic]

end Omega.Zeta
