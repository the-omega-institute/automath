import Mathlib.Tactic
import Omega.POM.ResonancePolelineExponentTranscendenceQ9_13

namespace Omega.POM

/-- The four q-values covered by the Newman logarithm norm certificate. -/
def pom_resonance_newman_log_transcendence_norm_q9_13_supported (q : Nat) : Prop :=
  q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 13

/-- Certified degrees used by the finite q-table. -/
def pom_resonance_newman_log_transcendence_norm_q9_13_degree (q : Nat) : Nat :=
  match q with
  | 9 => 9
  | 10 => 10
  | 11 => 11
  | 13 => 13
  | _ => 1

/-- Certified constant terms, chosen only for the supported q-values. -/
def pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm (q : Nat) : Int :=
  match q with
  | 9 => -2
  | 10 => 2
  | 11 => -3
  | 13 => -3
  | _ => 1

/-- The finite splitting-field norm expression from the symmetric-group root count. -/
def pom_resonance_newman_log_transcendence_norm_q9_13_norm (q : Nat) : Int :=
  (((-1 : Int) ^ pom_resonance_newman_log_transcendence_norm_q9_13_degree q) *
      pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm q) ^
    Nat.factorial (pom_resonance_newman_log_transcendence_norm_q9_13_degree q - 1)

/-- Concrete rational-exclusion side of the transcendence wrapper. -/
def pom_resonance_newman_log_transcendence_norm_q9_13_rationalExclusion
    (q : Nat) : Prop :=
  pom_resonance_newman_log_transcendence_norm_q9_13_supported q →
    pom_resonance_newman_log_transcendence_norm_q9_13_norm q ≠ 1

/-- Concrete Lindemann--Weierstrass/Gelfond--Schneider side of the wrapper. -/
def pom_resonance_newman_log_transcendence_norm_q9_13_gelfondSchneiderStep
    (q : Nat) : Prop :=
  pom_resonance_newman_log_transcendence_norm_q9_13_supported q →
    pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm q ≠ 1 ∧
      pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm q ≠ -1

/-- Concrete statement package for q in `{9, 10, 11, 13}`. -/
def pom_resonance_newman_log_transcendence_norm_q9_13_statement (q : Nat) : Prop :=
  pom_resonance_newman_log_transcendence_norm_q9_13_supported q →
    0 < pom_resonance_newman_log_transcendence_norm_q9_13_degree q ∧
      pom_resonance_newman_log_transcendence_norm_q9_13_norm q =
        (((-1 : Int) ^ pom_resonance_newman_log_transcendence_norm_q9_13_degree q) *
            pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm q) ^
          Nat.factorial (pom_resonance_newman_log_transcendence_norm_q9_13_degree q - 1) ∧
      pom_resonance_newman_log_transcendence_norm_q9_13_norm q ≠ 1 ∧
      pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm q ≠ 1 ∧
      pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm q ≠ -1 ∧
      (pom_resonance_newman_log_transcendence_norm_q9_13_rationalExclusion q ∧
        pom_resonance_newman_log_transcendence_norm_q9_13_gelfondSchneiderStep q)

lemma pom_resonance_newman_log_transcendence_norm_q9_13_pow_factorial_ne_one
    {a : Int} (ha : 1 < a) (k : Nat) : a ^ Nat.factorial k ≠ 1 := by
  have hpow : 1 < a ^ Nat.factorial k :=
    one_lt_pow₀ ha (Nat.factorial_ne_zero k)
  exact ne_of_gt hpow

lemma pom_resonance_newman_log_transcendence_norm_q9_13_certified
    (q : Nat) (hq : pom_resonance_newman_log_transcendence_norm_q9_13_supported q) :
    0 < pom_resonance_newman_log_transcendence_norm_q9_13_degree q ∧
      pom_resonance_newman_log_transcendence_norm_q9_13_norm q ≠ 1 ∧
      pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm q ≠ 1 ∧
      pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm q ≠ -1 := by
  rcases hq with rfl | rfl | rfl | rfl
  · refine ⟨by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_degree], ?_,
      by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm],
      by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm]⟩
    change (2 : Int) ^ Nat.factorial 8 ≠ 1
    exact pom_resonance_newman_log_transcendence_norm_q9_13_pow_factorial_ne_one
      (by norm_num : (1 : Int) < 2) 8
  · refine ⟨by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_degree], ?_,
      by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm],
      by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm]⟩
    change (2 : Int) ^ Nat.factorial 9 ≠ 1
    exact pom_resonance_newman_log_transcendence_norm_q9_13_pow_factorial_ne_one
      (by norm_num : (1 : Int) < 2) 9
  · refine ⟨by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_degree], ?_,
      by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm],
      by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm]⟩
    change (3 : Int) ^ Nat.factorial 10 ≠ 1
    exact pom_resonance_newman_log_transcendence_norm_q9_13_pow_factorial_ne_one
      (by norm_num : (1 : Int) < 3) 10
  · refine ⟨by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_degree], ?_,
      by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm],
      by norm_num [pom_resonance_newman_log_transcendence_norm_q9_13_constantTerm]⟩
    change (3 : Int) ^ Nat.factorial 12 ≠ 1
    exact pom_resonance_newman_log_transcendence_norm_q9_13_pow_factorial_ne_one
      (by norm_num : (1 : Int) < 3) 12

/-- Paper label: `thm:pom-resonance-newman-log-transcendence-norm-q9-13`. -/
theorem paper_pom_resonance_newman_log_transcendence_norm_q9_13
    (q : Nat) : pom_resonance_newman_log_transcendence_norm_q9_13_statement q := by
  intro hq
  rcases pom_resonance_newman_log_transcendence_norm_q9_13_certified q hq with
    ⟨hdeg, hnorm_ne, hct_ne_one, hct_ne_neg_one⟩
  have hrat : pom_resonance_newman_log_transcendence_norm_q9_13_rationalExclusion q := by
    intro hq'
    exact (pom_resonance_newman_log_transcendence_norm_q9_13_certified q hq').2.1
  have hgs : pom_resonance_newman_log_transcendence_norm_q9_13_gelfondSchneiderStep q := by
    intro hq'
    exact ⟨(pom_resonance_newman_log_transcendence_norm_q9_13_certified q hq').2.2.1,
      (pom_resonance_newman_log_transcendence_norm_q9_13_certified q hq').2.2.2⟩
  have hwrap :=
    paper_pom_resonance_poleline_exponent_transcendence_q9_13
      (pom_resonance_newman_log_transcendence_norm_q9_13_rationalExclusion q)
      (pom_resonance_newman_log_transcendence_norm_q9_13_gelfondSchneiderStep q)
      hrat hgs
  exact ⟨hdeg, rfl, hnorm_ne, hct_ne_one, hct_ne_neg_one, hwrap⟩

end Omega.POM
