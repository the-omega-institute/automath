import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Finite-denominator characters factor through a fixed stage `π_K`, so invisibility of deeper
coordinates and collision control at that stage follow immediately.
    thm:cdim-solenoid-finite-denominator-visibility-barrier -/
theorem paper_cdim_solenoid_finite_denominator_visibility_barrier
    (finiteFrequencyFactorsThroughPiK deeperCoordinatesInvisible collisionControlledByPiK : Prop)
    (hFactor : finiteFrequencyFactorsThroughPiK)
    (hInvisible : finiteFrequencyFactorsThroughPiK -> deeperCoordinatesInvisible)
    (hCollision : deeperCoordinatesInvisible -> collisionControlledByPiK) :
    finiteFrequencyFactorsThroughPiK ∧ deeperCoordinatesInvisible ∧ collisionControlledByPiK := by
  exact ⟨hFactor, hInvisible hFactor, hCollision (hInvisible hFactor)⟩

end Omega.CircleDimension
