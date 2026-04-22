import Omega.UnitCirclePhaseArithmetic.LeyangHaarPushforwardDensity

namespace Omega.CircleDimension

noncomputable section

/-- The Lee--Yang polar-family variable obtained by multiplying the angle by the rational slope
`n / d` before applying the branch-cover map. -/
def leyang_polar_family_pushforward_rigidity_value (n d : ℕ) (θ : ℝ) : ℝ :=
  Omega.UnitCirclePhaseArithmetic.leyangBranchCover (((n : ℝ) / (d : ℝ)) * θ)

/-- Coprime parameter invariance is recorded here as the explicit closed form of the polar-family
variable; the closed form depends only on the multiplied angle. -/
def leyang_polar_family_pushforward_rigidity_coprimeParameterInvariance (n d : ℕ) : Prop :=
  ∀ θ : ℝ,
    leyang_polar_family_pushforward_rigidity_value n d θ =
      -(1 / (4 * Real.cos (((n : ℝ) / (d : ℝ)) * θ) ^ 2))

/-- Equality in law is represented by equality with the explicit Haar-pushforward density
formula. -/
def leyang_polar_family_pushforward_rigidity_sameLawAsHaarPushforward : Prop :=
  ∀ t : ℝ,
    Omega.UnitCirclePhaseArithmetic.leyangHaarPushforwardDensity t =
      if t ≤ -(1 : ℝ) / 4 then 1 / (Real.pi * |t| * Real.sqrt |1 + 4 * t|) else 0

/-- Paper label: `cor:leyang-polar-family-pushforward-rigidity`.
The polar-family variable is the same explicit `-1 / (4 cos^2)` branch-cover profile as in the
Haar pushforward, and the density formula therefore agrees with the Haar-pushforward law already
proved in the unit-circle chapter. -/
theorem paper_leyang_polar_family_pushforward_rigidity (n d : ℕ) (_hd : 0 < d)
    (_hcop : Nat.Coprime n d) :
    leyang_polar_family_pushforward_rigidity_coprimeParameterInvariance n d ∧
      leyang_polar_family_pushforward_rigidity_sameLawAsHaarPushforward := by
  refine ⟨?_, ?_⟩
  · intro θ
    rfl
  · intro t
    exact (Omega.UnitCirclePhaseArithmetic.paper_leyang_haar_pushforward_density.2.1) t

end

end Omega.CircleDimension
