import Mathlib.Tactic
import Omega.POM.DerivedFoldRenyiDimensionTranscendenceQ4Q5Q16Q17
import Omega.POM.ResonanceS13FrobeniusCycleCertificateQ16Q17

namespace Omega.POM

/-- The audited Newman-ratio degree at the two resonance parameters. -/
def pom_resonance_newman_uq_degree_norm_q16_q17_degree (q : ℕ) : ℕ :=
  pom_resonance_s13_frobenius_cycle_certificate_q16_q17_degree q

/-- The audited Newman norm seed at `q = 16, 17`. -/
def pom_resonance_newman_uq_degree_norm_q16_q17_norm (q : ℕ) : ℚ :=
  if q = 16 then
    derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u16_norm
  else if q = 17 then
    derived_fold_renyi_dimension_transcendence_q4_q5_q16_q17_u17_norm
  else
    0

/-- The finite constant term data for the two audited resonance polynomials. -/
def pom_resonance_newman_uq_degree_norm_q16_q17_constant (q : ℕ) : ℕ :=
  if q = 16 then 8 else if q = 17 then 673948170 else 0

/-- Paper-facing concrete package for the `q = 16,17` degree and norm law. -/
def pom_resonance_newman_uq_degree_norm_q16_q17_statement : Prop :=
  pom_resonance_s13_frobenius_cycle_certificate_q16_q17_statement ∧
    pom_resonance_newman_uq_degree_norm_q16_q17_degree 16 = 13 ∧
    pom_resonance_newman_uq_degree_norm_q16_q17_degree 17 = 13 ∧
    momentCharpolyEval
        [2, 1611, 62312, 2559407, -24862788, -585266591, 62312, -44606766, 24862794,
          255692, -124624, 8, -8] 0 =
      pom_resonance_newman_uq_degree_norm_q16_q17_constant 16 ∧
    momentCharpolyEval
        [2, 2599, 125872, 6569850, -96034590, -2764163954, -643026032,
          -15022392733, 769974566, 15329386299, 642908352, 1347896340, -673948170]
          0 =
      pom_resonance_newman_uq_degree_norm_q16_q17_constant 17 ∧
    pom_resonance_newman_uq_degree_norm_q16_q17_norm 16 = -((2 : ℚ) ^ 205) ∧
    pom_resonance_newman_uq_degree_norm_q16_q17_norm 16 ≠ 1 ∧
    pom_resonance_newman_uq_degree_norm_q16_q17_norm 16 ≠ -1 ∧
    pom_resonance_newman_uq_degree_norm_q16_q17_norm 17 =
      (2 : ℚ) ^ (13 * 17) / (-(673948170 : ℚ)) ∧
    pom_resonance_newman_uq_degree_norm_q16_q17_norm 17 ≠ 1 ∧
    pom_resonance_newman_uq_degree_norm_q16_q17_norm 17 ≠ -1

/-- Paper label: `thm:pom-resonance-newman-uq-degree-norm-q16-q17`. -/
theorem paper_pom_resonance_newman_uq_degree_norm_q16_q17 :
    pom_resonance_newman_uq_degree_norm_q16_q17_statement := by
  refine ⟨paper_pom_resonance_s13_frobenius_cycle_certificate_q16_q17, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

end Omega.POM
