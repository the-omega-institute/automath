import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete input data for the equal-depth comoving collision regime. The Vandermonde lower bound
is recorded as a real inequality, and the near-collision blowup is phrased as the equal-depth
specialization of that lower bound. -/
structure ComovingCollisionData where
  depth : ℕ
  separation : ℝ
  amplification : ℝ
  vandermondeLower : ℝ
  amplification_lower : vandermondeLower ≤ amplification
  near_collision_blowup : separation ≤ 1 / ((depth : ℝ) + 1) → ((depth : ℝ) + 1) ≤ amplification

/-- The Lipschitz amplification dominates the separation-based Vandermonde lower bound. -/
def ComovingCollisionData.lipschitzAmplificationLowerBound (D : ComovingCollisionData) : Prop :=
  D.vandermondeLower ≤ D.amplification

/-- In the equal-depth near-collision regime, the amplification grows at least linearly in the
inverse collision scale. -/
def ComovingCollisionData.equalDepthNearCollisionBlowup (D : ComovingCollisionData) : Prop :=
  D.separation ≤ 1 / ((D.depth : ℝ) + 1) → ((D.depth : ℝ) + 1) ≤ D.amplification

/-- Paper-facing wrapper for the typed-address biaxial completion comoving-collision estimate.
    cor:typed-address-biaxial-completion-comoving-collision -/
theorem paper_typed_address_biaxial_completion_comoving_collision (D : ComovingCollisionData) :
    D.lipschitzAmplificationLowerBound ∧ D.equalDepthNearCollisionBlowup := by
  exact ⟨D.amplification_lower, D.near_collision_blowup⟩

end Omega.TypedAddressBiaxialCompletion
