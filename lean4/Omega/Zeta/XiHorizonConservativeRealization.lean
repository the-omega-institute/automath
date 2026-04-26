import Mathlib.Analysis.Complex.Basic
import Omega.CircleDimension.HorizonCarathSchurEquivalence

namespace Omega.Zeta

/-- The horizon Schur transform attached to a Carathéodory field. -/
noncomputable def xiHorizonSchurTransfer (C : ℂ → ℂ) : ℂ → ℂ :=
  fun w => (C w - 1) / (C w + 1)

/-- Scalar conservative realization package extracted from the Cayley transform: the transfer
function is exactly the horizon Schur transform, the denominator is pole-free in the admissible
region, and the transfer value is contractive. -/
def XiHorizonConservativeRealization (C S : ℂ → ℂ) : Prop :=
  ∀ w, S w = xiHorizonSchurTransfer C w ∧ C w + 1 ≠ 0 ∧ ‖S w‖ ≤ 1

/-- CMV normal-form realization in this scalar packaging: the transfer function is precisely the
Schur transform of the horizon Carathéodory field. -/
def XiHorizonCMVRealization (C S : ℂ → ℂ) : Prop :=
  ∀ w, S w = xiHorizonSchurTransfer C w

/-- Pole-free stability on the interior domain. -/
def XiHorizonPoleFreeStability (C : ℂ → ℂ) : Prop :=
  Omega.CircleDimension.xiHorizonBoundaryOnlySingularity C

/-- Carathéodory positivity yields the scalar conservative realization, its CMV normal form, and
the absence of interior poles for the horizon Schur transform.
    thm:xi-horizon-conservative-realization -/
theorem paper_xi_horizon_conservative_realization (C S : ℂ → ℂ)
    (hS : ∀ w, S w = xiHorizonSchurTransfer C w)
    (hCarath : ∀ w, 0 ≤ Complex.re (C w)) :
    XiHorizonConservativeRealization C S ∧
      XiHorizonCMVRealization C S ∧
      XiHorizonPoleFreeStability C := by
  have hBase := Omega.CircleDimension.paper_xi_horizon_carath_schur_equivalence C S hS
  refine ⟨?_, ?_, hBase.2⟩
  · intro w
    have hw := (hBase.1 w).1 (hCarath w)
    exact ⟨hS w, hw.1, hw.2⟩
  · intro w
    exact hS w

end Omega.Zeta
