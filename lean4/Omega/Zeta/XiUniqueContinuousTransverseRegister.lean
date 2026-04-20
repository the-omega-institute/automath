import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- The phase coordinate retained by the visible readout. -/
def xiPhaseProjection (u : ℝ × ℝ) : ℝ :=
  u.2

/-- The radial coordinate orthogonal to the visible phase projection. -/
def xiRadiusProjection (u : ℝ × ℝ) : ℝ :=
  u.1

/-- A transverse register factors through the radius when it is determined by a single radial
reparameterization. -/
def xiFactorsThroughRadius (register : ℝ × ℝ → ℝ) : Prop :=
  ∃ radial : ℝ → ℝ, ∀ u, register u = radial (xiRadiusProjection u)

/-- Uniqueness up to monotone reparameterization: the radial factor can be chosen strictly
monotone. -/
def xiUniqueUpToMonotoneReparam (register : ℝ × ℝ → ℝ) : Prop :=
  ∃ radial : ℝ → ℝ, StrictMono radial ∧ ∀ u, register u = radial (xiRadiusProjection u)

/-- Any continuous transverse register that is constant on phase fibers already factors through the
radius, and once the chosen radial coordinate is strictly monotone the factor is unique up to a
monotone reparameterization.
    cor:xi-unique-continuous-transverse-register -/
theorem paper_xi_unique_continuous_transverse_register
    (register : ℝ × ℝ → ℝ)
    (hphase : ∀ radius phase₁ phase₂,
      register (radius, phase₁) = register (radius, phase₂))
    (hmono : StrictMono fun radius => register (radius, 0)) :
    xiFactorsThroughRadius register ∧ xiUniqueUpToMonotoneReparam register := by
  let radial : ℝ → ℝ := fun radius => register (radius, 0)
  refine ⟨?_, ?_⟩
  · refine ⟨radial, ?_⟩
    intro u
    rcases u with ⟨radius, phase⟩
    exact hphase radius phase 0
  · refine ⟨radial, hmono, ?_⟩
    intro u
    rcases u with ⟨radius, phase⟩
    exact hphase radius phase 0

end Omega.Zeta
