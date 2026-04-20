import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Omega.GU.JoukowskyEllipticTwoScaleStokesMean

namespace Omega.GU

open Omega.GU.LeyangHolographicN2

/-- Concrete notation bundle for exponentiating the two-scale Stokes mean identity. -/
structure GroupJGEllipticTwoScaleData where
  r : ℂ
  z : ℂ
  z₁ : ℂ
  z₂ : ℂ
  hr : r ≠ 0
  hz : z ≠ 0
  hP : P z z₁ z₂ ≠ 0
  hR : quadraticReciprocalEval (r ^ 2 * z) z₁ z₂ ≠ 0

namespace GroupJGEllipticTwoScaleData

/-- Multiplicative version of the two-scale Joukowsky/Mahler factorization. -/
def exponentialMahlerFactorization (D : GroupJGEllipticTwoScaleData) : Prop :=
  Real.exp (joukowskyEllipseTwoScaleStokesMean D.r D.z D.z₁ D.z₂) =
    Real.exp (circleFactorLogMean D.r D.z D.z₁ D.z₂)

end GroupJGEllipticTwoScaleData

/-- Exponentiating the already verified two-scale Stokes-mean theorem yields the multiplicative
Mahler factorization immediately.
    cor:group-jg-elliptic-two-scale-mahler-multiplicative -/
theorem paper_group_jg_elliptic_two_scale_mahler_multiplicative
    (D : GroupJGEllipticTwoScaleData) : D.exponentialMahlerFactorization := by
  dsimp [GroupJGEllipticTwoScaleData.exponentialMahlerFactorization]
  exact congrArg Real.exp <|
    paper_group_jg_elliptic_two_scale_stokes_mean D.r D.z D.z₁ D.z₂ D.hr D.hz D.hP D.hR

end Omega.GU
