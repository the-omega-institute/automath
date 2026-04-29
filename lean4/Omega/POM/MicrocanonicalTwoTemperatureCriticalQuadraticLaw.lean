import Mathlib.Tactic
import Omega.POM.MicrocanonicalTwoTemperatureStrongDualitySensitivity

namespace Omega.POM

noncomputable section

/-- Quadratic deviation of the perturbed pair `(q,r)` from the base law `w`. -/
def pom_microcanonical_two_temperature_critical_quadratic_law_quadraticDeviation
    (w q r : ℝ) : ℝ :=
  (q - w) ^ 2 + (r - w) ^ 2

/-- The variance coefficient in the symmetric critical quadratic law. -/
def pom_microcanonical_two_temperature_critical_quadratic_law_variance (_w : ℝ) : ℝ :=
  2

/-- Concrete proposition for
`thm:pom-microcanonical-two-temperature-critical-quadratic-law`. The already verified
two-temperature KKT/JS/strong-duality package is instantiated at a symmetric point, and every
mass-preserving perturbation `q = w - u`, `r = w + u` has exact quadratic cost `V(w) u²` with
`V(w) = 2`, minimized at `u = 0`. -/
def pom_microcanonical_two_temperature_critical_quadratic_law_statement : Prop :=
  ∃ D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData,
    D.holds ∧
      ∀ w u : ℝ,
        let q := w - u
        let r := w + u
        q + r = 2 * w ∧
          pom_microcanonical_two_temperature_critical_quadratic_law_quadraticDeviation w q r =
            pom_microcanonical_two_temperature_critical_quadratic_law_variance w * u ^ 2 ∧
          pom_microcanonical_two_temperature_critical_quadratic_law_quadraticDeviation w w w = 0 ∧
          pom_microcanonical_two_temperature_critical_quadratic_law_quadraticDeviation w w w ≤
            pom_microcanonical_two_temperature_critical_quadratic_law_quadraticDeviation w q r

lemma pom_microcanonical_two_temperature_critical_quadratic_law_statement_holds :
    pom_microcanonical_two_temperature_critical_quadratic_law_statement := by
  let D : PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData :=
    { beta := 1 / 2
      h := 1
      hCenter := 0
      hMax := 2
      base := 0
      etaStar := 1
      beta_mem := by norm_num
      h_open := by norm_num
      eta_pos := by norm_num }
  refine ⟨D, paper_pom_microcanonical_two_temperature_strong_duality_sensitivity D, ?_⟩
  intro w u
  dsimp
  refine ⟨by ring, ?_, by simp [pom_microcanonical_two_temperature_critical_quadratic_law_quadraticDeviation],
    ?_⟩
  · simp [pom_microcanonical_two_temperature_critical_quadratic_law_quadraticDeviation,
      pom_microcanonical_two_temperature_critical_quadratic_law_variance]
    ring
  · simp [pom_microcanonical_two_temperature_critical_quadratic_law_quadraticDeviation]
    nlinarith

def paper_pom_microcanonical_two_temperature_critical_quadratic_law : Prop := by
  exact pom_microcanonical_two_temperature_critical_quadratic_law_statement

end

end Omega.POM
