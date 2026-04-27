import Mathlib.Tactic
import Omega.POM.ResonanceDiscSupportQ16Q17
import Omega.POM.ResonanceGaloisS13Q16Q17

namespace Omega.POM

/-- The ramified prime used for the `q = 16` Dedekind factorization certificate. -/
def pom_resonance_q16_q17_dedekind_factorization_prime16 : ℕ :=
  59

/-- The ramified prime used for the `q = 17` Dedekind factorization certificate. -/
def pom_resonance_q16_q17_dedekind_factorization_prime17 : ℕ :=
  62927

/-- Encoded `(ramification index, residue degree)` pairs for `q = 16`. -/
def pom_resonance_q16_q17_dedekind_factorization_pattern16 : List (ℕ × ℕ) :=
  [(2, 1), (1, 3), (1, 4), (1, 4)]

/-- Encoded `(ramification index, residue degree)` pairs for `q = 17`. -/
def pom_resonance_q16_q17_dedekind_factorization_pattern17 : List (ℕ × ℕ) :=
  [(2, 1), (1, 1), (1, 1), (1, 1), (1, 8)]

/-- Residue-degree vector for the displayed `q = 16` prime-ideal factorization. -/
def pom_resonance_q16_q17_dedekind_factorization_residue_degrees16 : List ℕ :=
  pom_resonance_q16_q17_dedekind_factorization_pattern16.map Prod.snd

/-- Residue-degree vector for the displayed `q = 17` prime-ideal factorization. -/
def pom_resonance_q16_q17_dedekind_factorization_residue_degrees17 : List ℕ :=
  pom_resonance_q16_q17_dedekind_factorization_pattern17.map Prod.snd

/-- Ramification-index vector for the displayed `q = 16` factorization. -/
def pom_resonance_q16_q17_dedekind_factorization_ramification16 : List ℕ :=
  pom_resonance_q16_q17_dedekind_factorization_pattern16.map Prod.fst

/-- Ramification-index vector for the displayed `q = 17` factorization. -/
def pom_resonance_q16_q17_dedekind_factorization_ramification17 : List ℕ :=
  pom_resonance_q16_q17_dedekind_factorization_pattern17.map Prod.fst

/-- Certificate-level Dedekind factorization statement for the two audited resonance windows. -/
def pom_resonance_q16_q17_dedekind_factorization_statement : Prop :=
  pom_resonance_disc_support_q16_q17_statement ∧
    (∀ D : pom_resonance_galois_s13_q16_17_certificate,
      pom_resonance_galois_s13_q16_17_conclusion D) ∧
    pom_resonance_q16_q17_dedekind_factorization_prime16 = 59 ∧
    pom_resonance_q16_q17_dedekind_factorization_prime17 = 62927 ∧
    pom_resonance_q16_q17_dedekind_factorization_residue_degrees16 = [1, 3, 4, 4] ∧
    pom_resonance_q16_q17_dedekind_factorization_residue_degrees17 = [1, 1, 1, 1, 8] ∧
    pom_resonance_q16_q17_dedekind_factorization_ramification16 = [2, 1, 1, 1] ∧
    pom_resonance_q16_q17_dedekind_factorization_ramification17 = [2, 1, 1, 1, 1] ∧
    (pom_resonance_q16_q17_dedekind_factorization_pattern16.map
        (fun ef => ef.1 * ef.2)).sum = 13 ∧
    (pom_resonance_q16_q17_dedekind_factorization_pattern17.map
        (fun ef => ef.1 * ef.2)).sum = 13

/-- Paper label: `prop:pom-resonance-q16-q17-dedekind-factorization`. -/
theorem paper_pom_resonance_q16_q17_dedekind_factorization :
    pom_resonance_q16_q17_dedekind_factorization_statement := by
  refine ⟨paper_pom_resonance_disc_support_q16_q17, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro D
    exact paper_pom_resonance_galois_s13_q16_17 D
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide

end Omega.POM
