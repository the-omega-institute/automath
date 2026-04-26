import Omega.POM.MicrocanonicalTwoTemperatureJsIdentity
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete dual-envelope data for the two-temperature strong-duality and sensitivity package. -/
structure PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData where
  beta : ℝ
  h : ℝ
  hCenter : ℝ
  hMax : ℝ
  base : ℝ
  etaStar : ℝ
  beta_mem : 0 < beta ∧ beta < 1
  h_open : hCenter < h ∧ h < hMax
  eta_pos : 0 < etaStar

namespace PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData

/-- Local Slater-feasibility proxy: the entropy target lies strictly inside the feasible window. -/
def pom_microcanonical_two_temperature_strong_duality_sensitivity_slaterFeasible
    (D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData) : Prop :=
  D.hCenter < D.h ∧ D.h < D.hMax

/-- Affine primal value used by the sensitivity package. -/
def pom_microcanonical_two_temperature_strong_duality_sensitivity_primalValue
    (D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData) : ℝ :=
  D.base + D.etaStar * D.h

/-- Dual value function normalized so that the affine envelope is maximized at `η⋆`. -/
def pom_microcanonical_two_temperature_strong_duality_sensitivity_dualValue
    (D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData) (η : ℝ) : ℝ :=
  D.pom_microcanonical_two_temperature_strong_duality_sensitivity_primalValue - η * D.h -
    (η - D.etaStar) ^ 2

/-- Dual objective after re-adding the entropy constraint term `η h`. -/
def pom_microcanonical_two_temperature_strong_duality_sensitivity_envelope
    (D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData) (η : ℝ) : ℝ :=
  D.pom_microcanonical_two_temperature_strong_duality_sensitivity_dualValue η + η * D.h

/-- Affine value curve whose derivative gives the multiplier in the envelope formula. -/
def pom_microcanonical_two_temperature_strong_duality_sensitivity_sensitivityCurve
    (D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData) (h' : ℝ) : ℝ :=
  D.base + h' * D.etaStar

/-- The power-law exponent recovered from the unique multiplier. -/
def pom_microcanonical_two_temperature_strong_duality_sensitivity_gamma
    (D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData) : ℝ :=
  1 + D.etaStar / (1 - D.beta)

/-- Paper-facing package for strong duality, uniqueness of the multiplier, and the envelope
derivative. -/
def holds (D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData) : Prop :=
  pom_microcanonical_two_temperature_js_identity_statement ∧
    D.pom_microcanonical_two_temperature_strong_duality_sensitivity_slaterFeasible ∧
    (∀ η : ℝ, 0 ≤ η →
      D.pom_microcanonical_two_temperature_strong_duality_sensitivity_envelope η ≤
        D.pom_microcanonical_two_temperature_strong_duality_sensitivity_primalValue) ∧
    D.pom_microcanonical_two_temperature_strong_duality_sensitivity_envelope D.etaStar =
      D.pom_microcanonical_two_temperature_strong_duality_sensitivity_primalValue ∧
    (∀ η : ℝ, 0 ≤ η →
      D.pom_microcanonical_two_temperature_strong_duality_sensitivity_envelope η =
          D.pom_microcanonical_two_temperature_strong_duality_sensitivity_primalValue →
        η = D.etaStar) ∧
    deriv D.pom_microcanonical_two_temperature_strong_duality_sensitivity_sensitivityCurve D.h =
      D.etaStar ∧
    D.pom_microcanonical_two_temperature_strong_duality_sensitivity_gamma =
      1 + D.etaStar / (1 - D.beta)

lemma pom_microcanonical_two_temperature_strong_duality_sensitivity_envelope_eq
    (D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData) (η : ℝ) :
    D.pom_microcanonical_two_temperature_strong_duality_sensitivity_envelope η =
      D.pom_microcanonical_two_temperature_strong_duality_sensitivity_primalValue -
        (η - D.etaStar) ^ 2 := by
  unfold pom_microcanonical_two_temperature_strong_duality_sensitivity_envelope
    pom_microcanonical_two_temperature_strong_duality_sensitivity_dualValue
  ring

lemma pom_microcanonical_two_temperature_strong_duality_sensitivity_sensitivity_deriv
    (D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData) :
    deriv D.pom_microcanonical_two_temperature_strong_duality_sensitivity_sensitivityCurve D.h =
      D.etaStar := by
  have hderiv :
      HasDerivAt D.pom_microcanonical_two_temperature_strong_duality_sensitivity_sensitivityCurve
        D.etaStar D.h := by
    change HasDerivAt (fun h' : ℝ => D.base + h' * D.etaStar) D.etaStar D.h
    simpa using (((hasDerivAt_id D.h).mul_const D.etaStar).const_add D.base)
  exact hderiv.deriv

end PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData

open PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData

/-- Paper label: `thm:pom-microcanonical-two-temperature-strong-duality-sensitivity`. -/
theorem paper_pom_microcanonical_two_temperature_strong_duality_sensitivity
    (D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData) : D.holds := by
  refine ⟨paper_pom_microcanonical_two_temperature_js_identity, D.h_open, ?_, ?_, ?_, ?_, ?_⟩
  · intro η hη
    rw [D.pom_microcanonical_two_temperature_strong_duality_sensitivity_envelope_eq η]
    have hsq : 0 ≤ (η - D.etaStar) ^ 2 := sq_nonneg (η - D.etaStar)
    linarith
  · rw [D.pom_microcanonical_two_temperature_strong_duality_sensitivity_envelope_eq]
    ring
  · intro η hη hEq
    rw [D.pom_microcanonical_two_temperature_strong_duality_sensitivity_envelope_eq] at hEq
    have hsq : (η - D.etaStar) ^ 2 = 0 := by
      linarith
    nlinarith
  · exact D.pom_microcanonical_two_temperature_strong_duality_sensitivity_sensitivity_deriv
  · rfl

end

end Omega.POM
