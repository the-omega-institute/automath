import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyDiscriminantFactorization

namespace Omega.Folding

/-- The quartic `F(μ,u)` from the gauge-anomaly pressure calculation, now viewed with the variable
order `(μ,u)`. -/
def gaugePressureQuartic (μ u : ℚ) : ℚ :=
  μ ^ 4 - μ ^ 3 - (2 * u + 1) * μ ^ 2 + (2 * u - u ^ 3) * μ + 2 * u

/-- The standard cubic resolvent attached to `gaugePressureQuartic`. -/
def gaugePressureResolvent (z u : ℚ) : ℚ :=
  z ^ 3 + (2 * u + 1) * z ^ 2 + (u ^ 3 - 10 * u) * z -
    (u ^ 6 - 4 * u ^ 4 + 20 * u ^ 2 + 10 * u)

/-- The textbook cubic resolvent formula for a monic quartic
`x^4 + a x^3 + b x^2 + c x + d`. -/
def gaugePressureStandardResolvent (z u : ℚ) : ℚ :=
  let a : ℚ := -1
  let b : ℚ := -(2 * u + 1)
  let c : ℚ := 2 * u - u ^ 3
  let d : ℚ := 2 * u
  z ^ 3 - b * z ^ 2 + (a * c - 4 * d) * z + (4 * b * d - a ^ 2 * d - c ^ 2)

/-- The discriminant of a monic cubic `z^3 + a z^2 + b z + c`. -/
def gaugePressureCubicDiscriminant (a b c : ℚ) : ℚ :=
  a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c - 27 * c ^ 2 + 18 * a * b * c

/-- The discriminant of the explicit cubic resolvent. -/
def gaugePressureResolventDiscriminant (u : ℚ) : ℚ :=
  gaugePressureCubicDiscriminant (2 * u + 1) (u ^ 3 - 10 * u)
    (-(u ^ 6 - 4 * u ^ 4 + 20 * u ^ 2 + 10 * u))

/-- Concrete parameter package for the resolvent/discriminant identity. -/
structure GaugePressureResolventDiscIdentityData where
  u : ℚ

namespace GaugePressureResolventDiscIdentityData

/-- The explicit cubic matches the standard quartic resolvent formula. -/
def resolventFormula (D : GaugePressureResolventDiscIdentityData) : Prop :=
  ∀ z : ℚ, gaugePressureResolvent z D.u = gaugePressureStandardResolvent z D.u

/-- The cubic-resolvent discriminant coincides with the quartic discriminant. -/
def discriminantCoincidence (D : GaugePressureResolventDiscIdentityData) : Prop :=
  gaugePressureResolventDiscriminant D.u = gaugeAnomalyQuarticDiscriminant D.u

/-- The shared discriminant factors through the existing `P10` polynomial. -/
def p10Factorization (D : GaugePressureResolventDiscIdentityData) : Prop :=
  gaugePressureResolventDiscriminant D.u = -D.u * (D.u - 1) * gaugeAnomalyP10 D.u

end GaugePressureResolventDiscIdentityData

open GaugePressureResolventDiscIdentityData

/-- Paper label: `prop:gauge-pressure-resolvent-disc-identity`. -/
theorem paper_root_unit_gauge_pressure_resolvent_disc_identity
    (D : GaugePressureResolventDiscIdentityData) :
    D.resolventFormula ∧ D.discriminantCoincidence ∧ D.p10Factorization := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    dsimp [gaugePressureResolvent, gaugePressureStandardResolvent]
    ring
  · unfold GaugePressureResolventDiscIdentityData.discriminantCoincidence
    dsimp [gaugePressureResolventDiscriminant, gaugePressureCubicDiscriminant,
      gaugeAnomalyQuarticDiscriminant]
    ring
  · unfold GaugePressureResolventDiscIdentityData.p10Factorization
    rw [show gaugePressureResolventDiscriminant D.u = gaugeAnomalyQuarticDiscriminant D.u by
      dsimp [gaugePressureResolventDiscriminant, gaugePressureCubicDiscriminant,
        gaugeAnomalyQuarticDiscriminant]
      ring]
    exact paper_fold_gauge_anomaly_discriminant_factorization D.u

/-- Paper label: `prop:gauge-pressure-resolvent-disc-identity`. -/
theorem paper_gauge_pressure_resolvent_disc_identity (D : GaugePressureResolventDiscIdentityData) :
    D.resolventFormula ∧ D.discriminantCoincidence ∧ D.p10Factorization := by
  exact paper_root_unit_gauge_pressure_resolvent_disc_identity D

end Omega.Folding
