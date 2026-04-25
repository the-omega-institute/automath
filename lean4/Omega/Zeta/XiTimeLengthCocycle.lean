import Mathlib.Tactic

namespace Omega.Zeta

universe u

/-- Concrete data for the time-length cocycle package: an associative composition law, a length
function, and a gauge correction. -/
structure XiTimeLengthCocycleData where
  W : Type u
  comp : W → W → W
  assoc : ∀ w₁ w₂ w₃, comp (comp w₁ w₂) w₃ = comp w₁ (comp w₂ w₃)
  len : W → ℤ
  beta : W → ℤ

namespace XiTimeLengthCocycleData

/-- The length defect `α(w₁,w₂) = ℓ(w₁ ◦ w₂) - ℓ(w₁) - ℓ(w₂)`. -/
def xi_time_length_cocycle_alpha (D : XiTimeLengthCocycleData) (w₁ w₂ : D.W) : ℤ :=
  D.len (D.comp w₁ w₂) - D.len w₁ - D.len w₂

/-- Gauge-shifted length `ℓ + β`. -/
def xi_time_length_cocycle_gaugeLen (D : XiTimeLengthCocycleData) (w : D.W) : ℤ :=
  D.len w + D.beta w

/-- The defect associated to the gauge-shifted length. -/
def xi_time_length_cocycle_gaugeAlpha (D : XiTimeLengthCocycleData) (w₁ w₂ : D.W) : ℤ :=
  D.xi_time_length_cocycle_gaugeLen (D.comp w₁ w₂) -
    D.xi_time_length_cocycle_gaugeLen w₁ -
    D.xi_time_length_cocycle_gaugeLen w₂

/-- The coboundary `δβ(w₁,w₂) = β(w₁ ◦ w₂) - β(w₁) - β(w₂)`. -/
def xi_time_length_cocycle_dbeta (D : XiTimeLengthCocycleData) (w₁ w₂ : D.W) : ℤ :=
  D.beta (D.comp w₁ w₂) - D.beta w₁ - D.beta w₂

/-- The defect satisfies the usual `2`-cocycle identity. -/
def twoCocycle (D : XiTimeLengthCocycleData) : Prop :=
  ∀ w₁ w₂ w₃,
    D.xi_time_length_cocycle_alpha (D.comp w₁ w₂) w₃ + D.xi_time_length_cocycle_alpha w₁ w₂ =
      D.xi_time_length_cocycle_alpha w₁ (D.comp w₂ w₃) +
        D.xi_time_length_cocycle_alpha w₂ w₃

/-- Replacing `ℓ` by `ℓ + β` changes the defect by the coboundary `δβ`. -/
def gaugeChangeIsCoboundary (D : XiTimeLengthCocycleData) : Prop :=
  ∀ w₁ w₂,
    D.xi_time_length_cocycle_gaugeAlpha w₁ w₂ =
      D.xi_time_length_cocycle_alpha w₁ w₂ + D.xi_time_length_cocycle_dbeta w₁ w₂

end XiTimeLengthCocycleData

open XiTimeLengthCocycleData

/-- Paper label: `prop:xi-time-length-cocycle`. The length defect attached to an associative
composition law is a `2`-cocycle, and a gauge shift of the length function changes it by the
explicit coboundary of the gauge term. -/
theorem paper_xi_time_length_cocycle (D : XiTimeLengthCocycleData) :
    D.twoCocycle ∧ D.gaugeChangeIsCoboundary := by
  constructor
  · intro w₁ w₂ w₃
    dsimp [XiTimeLengthCocycleData.twoCocycle, XiTimeLengthCocycleData.xi_time_length_cocycle_alpha]
    rw [D.assoc]
    ring
  · intro w₁ w₂
    dsimp [XiTimeLengthCocycleData.gaugeChangeIsCoboundary,
      XiTimeLengthCocycleData.xi_time_length_cocycle_gaugeAlpha,
      XiTimeLengthCocycleData.xi_time_length_cocycle_alpha,
      XiTimeLengthCocycleData.xi_time_length_cocycle_dbeta,
      XiTimeLengthCocycleData.xi_time_length_cocycle_gaugeLen]
    ring

end Omega.Zeta
