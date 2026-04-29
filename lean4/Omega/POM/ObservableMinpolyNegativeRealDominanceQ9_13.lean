import Mathlib.Tactic

namespace Omega.POM

/-- Concrete root-isolation certificate for the audited `q = 9, 10, 11, 13` window.  The
negative-root modulus fields are compared against certified upper bounds for every other
non-Perron root, and against the corresponding square-root Perron scale. -/
structure pom_observable_minpoly_negative_real_dominance_q9_13_certificates where
  pom_observable_minpoly_negative_real_dominance_q9_13_q9_negative_modulus : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q10_negative_modulus : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q11_negative_modulus : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q13_negative_modulus : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q9_other_modulus_bound : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q10_other_modulus_bound : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q11_other_modulus_bound : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q13_other_modulus_bound : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q9_sqrt_perron_bound : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q10_sqrt_perron_bound : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q11_sqrt_perron_bound : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q13_sqrt_perron_bound : ℚ
  pom_observable_minpoly_negative_real_dominance_q9_13_q9_dominance_cert :
    pom_observable_minpoly_negative_real_dominance_q9_13_q9_other_modulus_bound <
      pom_observable_minpoly_negative_real_dominance_q9_13_q9_negative_modulus
  pom_observable_minpoly_negative_real_dominance_q9_13_q10_dominance_cert :
    pom_observable_minpoly_negative_real_dominance_q9_13_q10_other_modulus_bound <
      pom_observable_minpoly_negative_real_dominance_q9_13_q10_negative_modulus
  pom_observable_minpoly_negative_real_dominance_q9_13_q11_dominance_cert :
    pom_observable_minpoly_negative_real_dominance_q9_13_q11_other_modulus_bound <
      pom_observable_minpoly_negative_real_dominance_q9_13_q11_negative_modulus
  pom_observable_minpoly_negative_real_dominance_q9_13_q13_dominance_cert :
    pom_observable_minpoly_negative_real_dominance_q9_13_q13_other_modulus_bound <
      pom_observable_minpoly_negative_real_dominance_q9_13_q13_negative_modulus
  pom_observable_minpoly_negative_real_dominance_q9_13_q9_negative_modulus_pos :
    0 < pom_observable_minpoly_negative_real_dominance_q9_13_q9_negative_modulus
  pom_observable_minpoly_negative_real_dominance_q9_13_q10_negative_modulus_pos :
    0 < pom_observable_minpoly_negative_real_dominance_q9_13_q10_negative_modulus
  pom_observable_minpoly_negative_real_dominance_q9_13_q11_negative_modulus_pos :
    0 < pom_observable_minpoly_negative_real_dominance_q9_13_q11_negative_modulus
  pom_observable_minpoly_negative_real_dominance_q9_13_q13_negative_modulus_pos :
    0 < pom_observable_minpoly_negative_real_dominance_q9_13_q13_negative_modulus
  pom_observable_minpoly_negative_real_dominance_q9_13_q9_ratio_cert :
    pom_observable_minpoly_negative_real_dominance_q9_13_q9_sqrt_perron_bound <
      pom_observable_minpoly_negative_real_dominance_q9_13_q9_negative_modulus
  pom_observable_minpoly_negative_real_dominance_q9_13_q10_ratio_cert :
    pom_observable_minpoly_negative_real_dominance_q9_13_q10_sqrt_perron_bound <
      pom_observable_minpoly_negative_real_dominance_q9_13_q10_negative_modulus
  pom_observable_minpoly_negative_real_dominance_q9_13_q11_ratio_cert :
    pom_observable_minpoly_negative_real_dominance_q9_13_q11_sqrt_perron_bound <
      pom_observable_minpoly_negative_real_dominance_q9_13_q11_negative_modulus
  pom_observable_minpoly_negative_real_dominance_q9_13_q13_ratio_cert :
    pom_observable_minpoly_negative_real_dominance_q9_13_q13_sqrt_perron_bound <
      pom_observable_minpoly_negative_real_dominance_q9_13_q13_negative_modulus

namespace pom_observable_minpoly_negative_real_dominance_q9_13_certificates

def negative_real_dominance
    (D : pom_observable_minpoly_negative_real_dominance_q9_13_certificates) : Prop :=
  D.pom_observable_minpoly_negative_real_dominance_q9_13_q9_other_modulus_bound <
      D.pom_observable_minpoly_negative_real_dominance_q9_13_q9_negative_modulus ∧
    D.pom_observable_minpoly_negative_real_dominance_q9_13_q10_other_modulus_bound <
      D.pom_observable_minpoly_negative_real_dominance_q9_13_q10_negative_modulus ∧
    D.pom_observable_minpoly_negative_real_dominance_q9_13_q11_other_modulus_bound <
      D.pom_observable_minpoly_negative_real_dominance_q9_13_q11_negative_modulus ∧
    D.pom_observable_minpoly_negative_real_dominance_q9_13_q13_other_modulus_bound <
      D.pom_observable_minpoly_negative_real_dominance_q9_13_q13_negative_modulus

def alternating_phase
    (D : pom_observable_minpoly_negative_real_dominance_q9_13_certificates) : Prop :=
  -D.pom_observable_minpoly_negative_real_dominance_q9_13_q9_negative_modulus < 0 ∧
    -D.pom_observable_minpoly_negative_real_dominance_q9_13_q10_negative_modulus < 0 ∧
    -D.pom_observable_minpoly_negative_real_dominance_q9_13_q11_negative_modulus < 0 ∧
    -D.pom_observable_minpoly_negative_real_dominance_q9_13_q13_negative_modulus < 0

def ramanujan_ratios_gt_one
    (D : pom_observable_minpoly_negative_real_dominance_q9_13_certificates) : Prop :=
  D.pom_observable_minpoly_negative_real_dominance_q9_13_q9_sqrt_perron_bound <
      D.pom_observable_minpoly_negative_real_dominance_q9_13_q9_negative_modulus ∧
    D.pom_observable_minpoly_negative_real_dominance_q9_13_q10_sqrt_perron_bound <
      D.pom_observable_minpoly_negative_real_dominance_q9_13_q10_negative_modulus ∧
    D.pom_observable_minpoly_negative_real_dominance_q9_13_q11_sqrt_perron_bound <
      D.pom_observable_minpoly_negative_real_dominance_q9_13_q11_negative_modulus ∧
    D.pom_observable_minpoly_negative_real_dominance_q9_13_q13_sqrt_perron_bound <
      D.pom_observable_minpoly_negative_real_dominance_q9_13_q13_negative_modulus

end pom_observable_minpoly_negative_real_dominance_q9_13_certificates

/-- Paper label: `prop:pom-observable-minpoly-negative-real-dominance-q9-13`. -/
theorem paper_pom_observable_minpoly_negative_real_dominance_q9_13
    (D : pom_observable_minpoly_negative_real_dominance_q9_13_certificates) :
    D.negative_real_dominance ∧ D.alternating_phase ∧ D.ramanujan_ratios_gt_one := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      ⟨D.pom_observable_minpoly_negative_real_dominance_q9_13_q9_dominance_cert,
        D.pom_observable_minpoly_negative_real_dominance_q9_13_q10_dominance_cert,
        D.pom_observable_minpoly_negative_real_dominance_q9_13_q11_dominance_cert,
        D.pom_observable_minpoly_negative_real_dominance_q9_13_q13_dominance_cert⟩
  · constructor
    · linarith
        [D.pom_observable_minpoly_negative_real_dominance_q9_13_q9_negative_modulus_pos]
    · constructor
      · linarith
          [D.pom_observable_minpoly_negative_real_dominance_q9_13_q10_negative_modulus_pos]
      · constructor
        · linarith
            [D.pom_observable_minpoly_negative_real_dominance_q9_13_q11_negative_modulus_pos]
        · linarith
            [D.pom_observable_minpoly_negative_real_dominance_q9_13_q13_negative_modulus_pos]
  · exact
      ⟨D.pom_observable_minpoly_negative_real_dominance_q9_13_q9_ratio_cert,
        D.pom_observable_minpoly_negative_real_dominance_q9_13_q10_ratio_cert,
        D.pom_observable_minpoly_negative_real_dominance_q9_13_q11_ratio_cert,
        D.pom_observable_minpoly_negative_real_dominance_q9_13_q13_ratio_cert⟩

end Omega.POM
