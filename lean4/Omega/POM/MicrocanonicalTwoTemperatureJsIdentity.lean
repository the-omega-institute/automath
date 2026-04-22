import Omega.POM.MicrocanonicalTwoTemperatureKktPowerLaw
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Chapter-local scalar entropy seed used to expand the Jensen--Shannon objective. -/
def pom_microcanonical_two_temperature_js_identity_entropy (x : ℝ) : ℝ :=
  -x * Real.log x

/-- Chapter-local scalar KL divergence seed. -/
def pom_microcanonical_two_temperature_js_identity_kl (x w : ℝ) : ℝ :=
  x * Real.log x - x * Real.log w

/-- Jensen--Shannon seed objective with affine mixing weight `β`. -/
def pom_microcanonical_two_temperature_js_identity_js (β q r w : ℝ) : ℝ :=
  β * pom_microcanonical_two_temperature_js_identity_kl q w +
    (1 - β) * pom_microcanonical_two_temperature_js_identity_kl r w

/-- The paper-facing package: retain the quadratic KKT seed from the previous file and record the
scalar Jensen--Shannon identity obtained by expanding the KL terms and canceling the mixed log term
under the affine constraint `w = β q + (1 - β) r`. -/
def pom_microcanonical_two_temperature_js_identity_statement : Prop :=
  (pomExistsUniqueMinimizer ∧ pomEntropyConstraintSaturated ∧ pomPowerLawCoupling) ∧
    ∀ β q r w : ℝ,
      w = β * q + (1 - β) * r →
        pom_microcanonical_two_temperature_js_identity_js β q r w =
          pom_microcanonical_two_temperature_js_identity_entropy w -
            β * pom_microcanonical_two_temperature_js_identity_entropy q -
            (1 - β) * pom_microcanonical_two_temperature_js_identity_entropy r

lemma pom_microcanonical_two_temperature_js_identity_expand
    (β q r w : ℝ) (hw : w = β * q + (1 - β) * r) :
    pom_microcanonical_two_temperature_js_identity_js β q r w =
      pom_microcanonical_two_temperature_js_identity_entropy w -
        β * pom_microcanonical_two_temperature_js_identity_entropy q -
        (1 - β) * pom_microcanonical_two_temperature_js_identity_entropy r := by
  dsimp [pom_microcanonical_two_temperature_js_identity_js,
    pom_microcanonical_two_temperature_js_identity_kl,
    pom_microcanonical_two_temperature_js_identity_entropy]
  calc
    β * (q * Real.log q - q * Real.log w) + (1 - β) * (r * Real.log r - r * Real.log w) =
      β * q * Real.log q + (1 - β) * r * Real.log r -
        ((β * q + (1 - β) * r) * Real.log w) := by
          ring
    _ = β * q * Real.log q + (1 - β) * r * Real.log r - (w * Real.log w) := by
          rw [hw]
    _ =
      -w * Real.log w - β * (-q * Real.log q) - (1 - β) * (-r * Real.log r) := by
          ring

/-- Paper label: `prop:pom-microcanonical-two-temperature-js-identity`. -/
theorem paper_pom_microcanonical_two_temperature_js_identity :
    pom_microcanonical_two_temperature_js_identity_statement := by
  refine ⟨paper_pom_microcanonical_two_temperature_kkt_power_law, ?_⟩
  intro β q r w hw
  exact pom_microcanonical_two_temperature_js_identity_expand β q r w hw

end

end Omega.POM
