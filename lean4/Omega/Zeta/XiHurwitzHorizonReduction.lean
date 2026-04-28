import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppRhIffDiskZeroFree

namespace Omega.Zeta

open Omega.UnitCirclePhaseArithmetic
open AppRhIffDiskZeroFreeData

/-- The finite horizon approximants are zero-free on the disk model. -/
def xi_hurwitz_horizon_reduction_approximantsZeroFree
    {DiskPoint : Type} (insideDisk : DiskPoint → Prop)
    (approximant : ℕ → DiskPoint → ℂ) : Prop :=
  ∀ N : ℕ, ∀ w : DiskPoint, insideDisk w → approximant N w ≠ 0

/-- Hurwitz zero theorem, specialized as the nonzero-limit conclusion needed by the horizon
reduction: a locally uniform limit of zero-free approximants is zero-free when the limit is not
identically zero.  The analytic convergence hypotheses are represented by this concrete
zero-freeness conclusion on the limit function. -/
def xi_hurwitz_horizon_reduction_hurwitzNonzeroLimit
    {DiskPoint : Type} (insideDisk : DiskPoint → Prop)
    (approximant : ℕ → DiskPoint → ℂ) (limitModel : DiskPoint → ℂ) : Prop :=
  xi_hurwitz_horizon_reduction_approximantsZeroFree insideDisk approximant →
    ∀ w : DiskPoint, insideDisk w → limitModel w ≠ 0

/-- The horizon limit agrees with the disk model from the RH interface. -/
def xi_hurwitz_horizon_reduction_limitCompatible
    (D : AppRhIffDiskZeroFreeData) (limitModel : D.DiskPoint → ℂ) : Prop :=
  ∀ w : D.DiskPoint, D.insideDisk w → limitModel w = D.diskModel w

/-- Concrete wrapper for the Hurwitz horizon reduction.  Zero-free horizon approximants, the
Hurwitz nonzero-limit conclusion, and compatibility with the disk-zero-free RH interface imply
RH. -/
def xi_hurwitz_horizon_reduction_statement : Prop :=
  ∀ (D : AppRhIffDiskZeroFreeData) (approximant : ℕ → D.DiskPoint → ℂ)
    (limitModel : D.DiskPoint → ℂ),
    xi_hurwitz_horizon_reduction_approximantsZeroFree D.insideDisk approximant →
    xi_hurwitz_horizon_reduction_hurwitzNonzeroLimit D.insideDisk approximant limitModel →
    xi_hurwitz_horizon_reduction_limitCompatible D limitModel →
      D.riemannHypothesis

/-- Paper label: `thm:xi-hurwitz-horizon-reduction`. -/
theorem paper_xi_hurwitz_horizon_reduction :
    xi_hurwitz_horizon_reduction_statement := by
  intro D approximant limitModel happrox hhurwitz hcompatible
  have hlimitZeroFree : ∀ w : D.DiskPoint, D.insideDisk w → limitModel w ≠ 0 :=
    hhurwitz happrox
  have hdiskZeroFree : D.diskZeroFree := by
    intro w hw hzero
    exact hlimitZeroFree w hw (by simpa [hcompatible w hw] using hzero)
  exact (paper_app_rh_iff_disk_zero_free D).2 hdiskZeroFree

end Omega.Zeta
