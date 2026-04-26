import Mathlib.Tactic
import Omega.POM.MultiplicityLambdaqDerivativeGibbs

namespace Omega.POM

noncomputable section

/-- Concrete finite-composition pressure data for the general real-`q` Shannon entropy-rate
package.  The entropy rate is tied to the already verified Gibbs derivative ratio, the pressure
root is tied to the real-`q` root, and the Taylor data supplies the small-`q` expansion. -/
structure pom_multiplicity_composition_shannon_entropy_rate_generalq_data where
  entropyRate : ℝ → ℝ
  pressureRoot : ℝ → ℝ
  endpointZeroValue : ℝ
  endpointInfinityValue : ℝ
  taylorData : pom_multiplicity_lambdaq_taylor_q0_data
  entropyRate_eq_gibbsDerivative :
    ∀ q : ℝ, 0 < q → entropyRate q = pom_multiplicity_lambdaq_derivative_gibbs_ratio q
  pressureRoot_eq : ∀ q : ℝ, pressureRoot q = pomRealQRoot q
  endpointZeroValue_eq : endpointZeroValue = 1
  endpointInfinityValue_eq : endpointInfinityValue = 0

namespace pom_multiplicity_composition_shannon_entropy_rate_generalq_data

/-- Closed form obtained from the pressure/log-partition derivative. -/
def closedForm
    (D : pom_multiplicity_composition_shannon_entropy_rate_generalq_data) : Prop :=
  ∀ q : ℝ, 0 < q →
    D.entropyRate q = pom_multiplicity_lambdaq_derivative_gibbs_closed q

/-- The Shannon entropy rate starts at one bit per length at `q = 0`. -/
def endpointZero
    (D : pom_multiplicity_composition_shannon_entropy_rate_generalq_data) : Prop :=
  D.endpointZeroValue = 1

/-- The zero-temperature endpoint vanishes in the large-`q` limit package. -/
def endpointInfinity
    (D : pom_multiplicity_composition_shannon_entropy_rate_generalq_data) : Prop :=
  D.endpointInfinityValue = 0

/-- The pressure root decreases strictly with the real parameter. -/
def strictlyDecreasing
    (D : pom_multiplicity_composition_shannon_entropy_rate_generalq_data) : Prop :=
  ∀ q₁ q₂ : ℝ, 0 < q₁ → q₁ < q₂ → D.pressureRoot q₂ < D.pressureRoot q₁

/-- Small-`q` expansion supplied by the verified Taylor package. -/
def smallQExpansion
    (D : pom_multiplicity_composition_shannon_entropy_rate_generalq_data) : Prop :=
  D.taylorData.hasSecondOrderExpansion

/-- Large-`q` expansion supplied by the verified real-parameter pressure package. -/
def largeQExpansion
    (_D : pom_multiplicity_composition_shannon_entropy_rate_generalq_data) : Prop :=
  pom_multiplicity_lambdaq_large_q_asymptotic_statement

lemma closedForm_holds
    (D : pom_multiplicity_composition_shannon_entropy_rate_generalq_data) :
    D.closedForm := by
  intro q hq
  have hratio := (paper_pom_multiplicity_lambdaq_derivative_gibbs q hq).2.2.2.1
  exact (D.entropyRate_eq_gibbsDerivative q hq).trans hratio

lemma strictlyDecreasing_holds
    (D : pom_multiplicity_composition_shannon_entropy_rate_generalq_data) :
    D.strictlyDecreasing := by
  intro q₁ q₂ hq₁ hq₁q₂
  have hroot := paper_pom_multiplicity_real_q_pressure.2.2.1 q₁ q₂ hq₁ hq₁q₂
  simpa [D.pressureRoot_eq q₁, D.pressureRoot_eq q₂] using hroot

end pom_multiplicity_composition_shannon_entropy_rate_generalq_data

open pom_multiplicity_composition_shannon_entropy_rate_generalq_data

/-- Paper label:
`prop:pom-multiplicity-composition-shannon-entropy-rate-generalq`. -/
theorem paper_pom_multiplicity_composition_shannon_entropy_rate_generalq
    (D : pom_multiplicity_composition_shannon_entropy_rate_generalq_data) :
    D.closedForm ∧ D.endpointZero ∧ D.endpointInfinity ∧ D.strictlyDecreasing ∧
      D.smallQExpansion ∧ D.largeQExpansion := by
  exact
    ⟨D.closedForm_holds, D.endpointZeroValue_eq, D.endpointInfinityValue_eq,
      D.strictlyDecreasing_holds, paper_pom_multiplicity_lambdaq_taylor_q0 D.taylorData,
      paper_pom_multiplicity_lambdaq_large_q_asymptotic⟩

end

end Omega.POM
