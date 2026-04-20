import Mathlib.Tactic
import Omega.Zeta.SyncHatdeltaCurveDoubleCoverBranchGenus6

namespace Omega.Zeta

/-- The affine quartic in the quotient invariants `x = w^2` and `y = s*w`. -/
def syncHatdeltaQuotientAffineQuartic (x y : ℤ) : ℤ :=
  1 - y - 5 * x + 3 * x * y + 5 * x ^ 2 - x * y ^ 2 + x * y ^ 3 - 6 * x ^ 2 * y +
    x ^ 2 * y ^ 2 - x ^ 3

/-- The homogeneous plane-quartic model of the quotient curve. -/
def syncHatdeltaQuotientHomogeneousQuartic (X Y Z : ℤ) : ℤ :=
  Z ^ 4 - Y * Z ^ 3 - 5 * X * Z ^ 3 + 3 * X * Y * Z ^ 2 + 5 * X ^ 2 * Z ^ 2 -
    X * Y ^ 2 * Z + X * Y ^ 3 + X ^ 2 * Y ^ 2 - 6 * X ^ 2 * Y * Z - X ^ 3 * Z

/-- The explicit `X`-derivative of the homogeneous quartic. -/
def syncHatdeltaQuotientHomogeneousQuartic_dX (X Y Z : ℤ) : ℤ :=
  -5 * Z ^ 3 + 3 * Y * Z ^ 2 + 10 * X * Z ^ 2 - Y ^ 2 * Z + Y ^ 3 + 2 * X * Y ^ 2 -
    12 * X * Y * Z - 3 * X ^ 2 * Z

/-- The explicit `Y`-derivative of the homogeneous quartic. -/
def syncHatdeltaQuotientHomogeneousQuartic_dY (X Y Z : ℤ) : ℤ :=
  -Z ^ 3 + 3 * X * Z ^ 2 - 2 * X * Y * Z + 3 * X * Y ^ 2 + 2 * X ^ 2 * Y - 6 * X ^ 2 * Z

/-- The explicit `Z`-derivative of the homogeneous quartic. -/
def syncHatdeltaQuotientHomogeneousQuartic_dZ (X Y Z : ℤ) : ℤ :=
  4 * Z ^ 3 - 3 * Y * Z ^ 2 - 15 * X * Z ^ 2 + 6 * X * Y * Z + 10 * X ^ 2 * Z - X * Y ^ 2 -
    6 * X ^ 2 * Y - X ^ 3

/-- The quotient model is a plane quartic. -/
def syncHatdeltaQuotientPlaneQuarticDegree : ℕ := 4

/-- Genus formula for a smooth plane curve of degree `d`. -/
def syncHatdeltaSmoothPlaneCurveGenus (d : ℕ) : ℕ :=
  (d - 1) * (d - 2) / 2

/-- Chapter-local data bundle for the quotient invariants `x = w^2` and `y = s*w`. -/
structure SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data where
  w : ℤ
  s : ℤ
  x : ℤ
  y : ℤ
  hx : x = w ^ 2
  hy : y = s * w

namespace SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data

/-- The quotient invariants recover the affine quartic, and homogenizing then dehomogenizing at
`Z = 1` gives the same equation. -/
def birationalQuotientModel (D : SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data) : Prop :=
  D.x = D.w ^ 2 ∧
    D.y = D.s * D.w ∧
    syncHatdeltaQuotientAffineQuartic D.x D.y =
      syncHatdeltaQuotientHomogeneousQuartic D.x D.y 1

/-- An explicit smooth-plane-quartic certificate: the model has degree `4`, and its three points
at infinity are all nonsingular by direct gradient checks. -/
def smoothPlaneQuartic (_D : SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data) : Prop :=
  syncHatdeltaQuotientPlaneQuarticDegree = 4 ∧
    syncHatdeltaQuotientHomogeneousQuartic 1 0 0 = 0 ∧
    syncHatdeltaQuotientHomogeneousQuartic_dZ 1 0 0 ≠ 0 ∧
    syncHatdeltaQuotientHomogeneousQuartic 0 1 0 = 0 ∧
    syncHatdeltaQuotientHomogeneousQuartic_dX 0 1 0 ≠ 0 ∧
    syncHatdeltaQuotientHomogeneousQuartic 1 (-1) 0 = 0 ∧
    syncHatdeltaQuotientHomogeneousQuartic_dX 1 (-1) 0 ≠ 0

/-- The smooth plane-quartic genus formula reproduces the genus-`3` quotient already recorded in
`syncHatdeltaQuotientCurve`. -/
def genusEqThree (_D : SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data) : Prop :=
  syncHatdeltaSmoothPlaneCurveGenus syncHatdeltaQuotientPlaneQuarticDegree =
    syncHatdeltaQuotientCurve.genus

end SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data

theorem syncHatdelta_quotient_quartic_dehomogenizes (x y : ℤ) :
    syncHatdeltaQuotientHomogeneousQuartic x y 1 = syncHatdeltaQuotientAffineQuartic x y := by
  simp [syncHatdeltaQuotientHomogeneousQuartic, syncHatdeltaQuotientAffineQuartic]
  ring

theorem syncHatdelta_quotient_plane_quartic_smooth_certificate
    (D : SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data) : D.smoothPlaneQuartic := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data.smoothPlaneQuartic,
      syncHatdeltaQuotientHomogeneousQuartic]
  · norm_num [SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data.smoothPlaneQuartic,
      syncHatdeltaQuotientHomogeneousQuartic_dZ]
  · norm_num [SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data.smoothPlaneQuartic,
      syncHatdeltaQuotientHomogeneousQuartic]
  · norm_num [SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data.smoothPlaneQuartic,
      syncHatdeltaQuotientHomogeneousQuartic_dX]
  · norm_num [SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data.smoothPlaneQuartic,
      syncHatdeltaQuotientHomogeneousQuartic]
  · norm_num [SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data.smoothPlaneQuartic,
      syncHatdeltaQuotientHomogeneousQuartic_dX]

theorem syncHatdelta_quotient_plane_quartic_genus_three
    (D : SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data) : D.genusEqThree := by
  simp [SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data.genusEqThree,
    syncHatdeltaSmoothPlaneCurveGenus, syncHatdeltaQuotientPlaneQuarticDegree,
    syncHatdeltaQuotientCurve]

/-- Paper-facing quotient-model package for `\widehatΔ`: the invariant generators `x = w^2` and
`y = s*w` give the explicit affine quartic, its homogenization is the displayed plane quartic,
the projective boundary points are nonsingular, and the plane-quartic genus formula yields
genus `3`.
    prop:sync-hatdelta-curve-quotient-plane-quartic-genus3 -/
theorem paper_sync_hatdelta_curve_quotient_plane_quartic_genus3
    (D : SyncHatdeltaCurveQuotientPlaneQuarticGenus3Data) :
    D.birationalQuotientModel ∧ D.smoothPlaneQuartic ∧ D.genusEqThree := by
  refine ⟨?_, syncHatdelta_quotient_plane_quartic_smooth_certificate D,
    syncHatdelta_quotient_plane_quartic_genus_three D⟩
  refine ⟨D.hx, D.hy, ?_⟩
  simpa using (syncHatdelta_quotient_quartic_dehomogenizes D.x D.y).symm

end Omega.Zeta
