import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.RootUnitCharacterPressureTensor

/-- A concrete package for the drift-ratio dense-band statement. `approxAngle μ η B` is a chosen
lattice direction at scale `B` whose Rayleigh quotient eventually stays within `η` of `μ`, while
`approxMem` and `approxSmallGap` record the lattice membership and gap control for that witness. -/
structure RootUnitDriftRatioData where
  Angle : Type
  muMin : ℝ
  muMax : ℝ
  R : Angle → ℝ
  angleLattice : ℕ → Set Angle
  smallGap : ℕ → Angle → Prop
  approxAngle : ℝ → ℝ → ℕ → Angle
  mu_order : muMin ≤ muMax
  approxMem : ∀ mu eta B, approxAngle mu eta B ∈ angleLattice B
  approxSmallGap : ∀ mu eta B, smallGap B (approxAngle mu eta B)
  approxEventuallyClose :
    ∀ mu eta : ℝ,
      muMin ≤ mu →
        mu ≤ muMax →
          0 < eta →
            ∃ B0 : ℕ, ∀ B ≥ B0, abs (R (approxAngle mu eta B) - mu) < eta

/-- Paper label: `thm:root-unit-drift-ratio-dense-band`. The concrete dense-band package records a
uniform interval `[muMin, muMax]` together with lattice witnesses that eventually approximate any
target drift ratio inside the band while preserving the small-gap property. -/
theorem paper_root_unit_drift_ratio_dense_band (D : RootUnitDriftRatioData) :
    D.muMin <= D.muMax ∧
      (∀ mu eta : ℝ, D.muMin <= mu -> mu <= D.muMax -> 0 < eta -> ∃ B0 : ℕ,
        ∀ B, B >= B0 -> ∃ theta : D.Angle,
          theta ∈ D.angleLattice B ∧ abs (D.R theta - mu) < eta ∧ D.smallGap B theta) := by
  refine ⟨D.mu_order, ?_⟩
  intro mu eta hmuMin hmuMax heta
  rcases D.approxEventuallyClose mu eta hmuMin hmuMax heta with ⟨B0, hclose⟩
  refine ⟨B0, ?_⟩
  intro B hB
  refine ⟨D.approxAngle mu eta B, D.approxMem mu eta B, hclose B hB, D.approxSmallGap mu eta B⟩

end Omega.RootUnitCharacterPressureTensor
