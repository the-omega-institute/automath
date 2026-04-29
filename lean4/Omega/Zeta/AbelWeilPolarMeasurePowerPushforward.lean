import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The polar eigenvalue attached to a spectral label and a base. -/
def abel_weil_polar_measure_power_pushforward_lambda (ρ b : ℕ) : ℕ :=
  b ^ ρ

/-- The argument-level phase used by the discrete polar package. -/
def abel_weil_polar_measure_power_pushforward_phase (ρ : ℕ) : ℕ :=
  ρ

/-- Concrete discrete polar spectral measure data for the power-pushforward statement. -/
structure abel_weil_polar_measure_power_pushforward_data where
  support : Finset ℕ
  weight : ℕ → ℝ
  base : ℕ
  observable : ℕ → ℝ

namespace abel_weil_polar_measure_power_pushforward_data

/-- The discrete polar integral against the packaged spectral measure. -/
def polarIntegral (D : abel_weil_polar_measure_power_pushforward_data) : ℝ :=
  Finset.sum D.support fun ρ =>
    D.weight ρ * D.observable (abel_weil_polar_measure_power_pushforward_lambda ρ D.base)

/-- The defining finite spectral sum for the same polar integral. -/
def definingPolarSum (D : abel_weil_polar_measure_power_pushforward_data) : ℝ :=
  Finset.sum D.support fun ρ =>
    D.weight ρ * D.observable (abel_weil_polar_measure_power_pushforward_lambda ρ D.base)

/-- The integral representation is the defining discrete spectral sum. -/
def polarIntegralRepresentation (D : abel_weil_polar_measure_power_pushforward_data) : Prop :=
  D.polarIntegral = D.definingPolarSum

/-- Compatibility of the spectral measure with the base power map. -/
def powerPushforwardCompatible (D : abel_weil_polar_measure_power_pushforward_data)
    (m : ℕ) : Prop :=
  ∀ ρ ∈ D.support,
    abel_weil_polar_measure_power_pushforward_lambda ρ (D.base ^ m) =
      (abel_weil_polar_measure_power_pushforward_lambda ρ D.base) ^ m

/-- Argument-level compatibility of phases under multiplication by `m`. -/
def phaseMultiplicationCompatible (D : abel_weil_polar_measure_power_pushforward_data)
    (m : ℕ) : Prop :=
  ∀ ρ ∈ D.support,
    abel_weil_polar_measure_power_pushforward_phase (m * ρ) =
      m * abel_weil_polar_measure_power_pushforward_phase ρ

end abel_weil_polar_measure_power_pushforward_data

/-- Paper label: `prop:abel-weil-polar-measure-power-pushforward`. -/
theorem paper_abel_weil_polar_measure_power_pushforward
    (D : abel_weil_polar_measure_power_pushforward_data) :
    D.polarIntegralRepresentation ∧ ∀ m : ℕ, 2 ≤ m →
      D.powerPushforwardCompatible m ∧ D.phaseMultiplicationCompatible m := by
  refine ⟨?_, ?_⟩
  · rfl
  · intro m _hm
    constructor
    · intro ρ _hρ
      calc
        abel_weil_polar_measure_power_pushforward_lambda ρ (D.base ^ m) =
            D.base ^ (m * ρ) := by
          rw [abel_weil_polar_measure_power_pushforward_lambda, pow_mul]
        _ = D.base ^ (ρ * m) := by rw [Nat.mul_comm]
        _ = (abel_weil_polar_measure_power_pushforward_lambda ρ D.base) ^ m := by
          rw [abel_weil_polar_measure_power_pushforward_lambda, pow_mul]
    · intro ρ _hρ
      rfl

end Omega.Zeta
