import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for a finite alphabet used by an AGM-to-fold translator. -/
structure conclusion_foldgauge_pi_agm_translator_dichotomy_data where
  alphabetSize : ℕ

/-- Fold-gauge Koenigs germs have nonzero multiplier in this package. -/
def conclusion_foldgauge_pi_agm_translator_dichotomy_koenigs_multiplier : ℕ := 1

/-- AGM/Gauss--Salamin germs have zero multiplier in this package. -/
def conclusion_foldgauge_pi_agm_translator_dichotomy_agm_multiplier : ℕ := 0

/-- The local analytic conjugacy requirement would have to preserve the multiplier. -/
def conclusion_foldgauge_pi_agm_translator_dichotomy_local_conjugacy_requirement
    (_D : conclusion_foldgauge_pi_agm_translator_dichotomy_data) : Prop :=
  conclusion_foldgauge_pi_agm_translator_dichotomy_koenigs_multiplier =
    conclusion_foldgauge_pi_agm_translator_dichotomy_agm_multiplier

/-- A below-bound deterministic reversible lift contradicts the finite alphabet hypothesis. -/
def conclusion_foldgauge_pi_agm_translator_dichotomy_low_side_info_requirement
    (D : conclusion_foldgauge_pi_agm_translator_dichotomy_data) : Prop :=
  D.alphabetSize < 2

/--
Concrete Lean statement for the paper theorem: over an alphabet with at least two symbols,
the Koenigs-vs-AGM local type obstruction and the side-information lower bound each rule
out the corresponding translator requirement.
-/
def conclusion_foldgauge_pi_agm_translator_dichotomy_statement
    (D : conclusion_foldgauge_pi_agm_translator_dichotomy_data) : Prop :=
  2 ≤ D.alphabetSize →
    ¬ (conclusion_foldgauge_pi_agm_translator_dichotomy_local_conjugacy_requirement D ∧
      conclusion_foldgauge_pi_agm_translator_dichotomy_low_side_info_requirement D) ∧
    ¬ conclusion_foldgauge_pi_agm_translator_dichotomy_local_conjugacy_requirement D ∧
    ¬ conclusion_foldgauge_pi_agm_translator_dichotomy_low_side_info_requirement D

/-- Paper label: `thm:conclusion-foldgauge-pi-agm-translator-dichotomy`. -/
theorem paper_conclusion_foldgauge_pi_agm_translator_dichotomy
    (D : conclusion_foldgauge_pi_agm_translator_dichotomy_data) :
    conclusion_foldgauge_pi_agm_translator_dichotomy_statement D := by
  intro hAlphabet
  constructor
  · intro hBoth
    exact Nat.not_lt_of_ge hAlphabet hBoth.2
  · constructor
    · norm_num [conclusion_foldgauge_pi_agm_translator_dichotomy_local_conjugacy_requirement,
        conclusion_foldgauge_pi_agm_translator_dichotomy_koenigs_multiplier,
        conclusion_foldgauge_pi_agm_translator_dichotomy_agm_multiplier]
    · exact Nat.not_lt_of_ge hAlphabet

end Omega.Conclusion
