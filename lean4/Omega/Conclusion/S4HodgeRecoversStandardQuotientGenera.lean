import Mathlib.Tactic
import Omega.Conclusion.S4HodgeDeterminesFixedpointCounts

namespace Omega.Conclusion

/-- The standard subgroup classes used for the quotient-genus table. -/
inductive conclusion_s4_hodge_recovers_standard_quotient_genera_subgroup
  | tau
  | delta
  | sigma3
  | sigma4
  | v4
  | s3
  | d8
  | a4
  | s4
  deriving DecidableEq

/-- Order of each standard subgroup class. -/
def conclusion_s4_hodge_recovers_standard_quotient_genera_order :
    conclusion_s4_hodge_recovers_standard_quotient_genera_subgroup → ℕ
  | .tau => 2
  | .delta => 2
  | .sigma3 => 3
  | .sigma4 => 4
  | .v4 => 4
  | .s3 => 6
  | .d8 => 8
  | .a4 => 12
  | .s4 => 24

/-- Number of transpositions in each standard subgroup class. -/
def conclusion_s4_hodge_recovers_standard_quotient_genera_transposition_count :
    conclusion_s4_hodge_recovers_standard_quotient_genera_subgroup → ℕ
  | .tau => 1
  | .delta => 0
  | .sigma3 => 0
  | .sigma4 => 0
  | .v4 => 0
  | .s3 => 3
  | .d8 => 2
  | .a4 => 0
  | .s4 => 6

/-- Number of double transpositions in each standard subgroup class. -/
def conclusion_s4_hodge_recovers_standard_quotient_genera_double_transposition_count :
    conclusion_s4_hodge_recovers_standard_quotient_genera_subgroup → ℕ
  | .tau => 0
  | .delta => 1
  | .sigma3 => 0
  | .sigma4 => 1
  | .v4 => 3
  | .s3 => 0
  | .d8 => 3
  | .a4 => 3
  | .s4 => 3

/-- Number of three-cycles in each standard subgroup class. -/
def conclusion_s4_hodge_recovers_standard_quotient_genera_three_cycle_count :
    conclusion_s4_hodge_recovers_standard_quotient_genera_subgroup → ℕ
  | .tau => 0
  | .delta => 0
  | .sigma3 => 2
  | .sigma4 => 0
  | .v4 => 0
  | .s3 => 2
  | .d8 => 0
  | .a4 => 8
  | .s4 => 8

/-- Number of four-cycles in each standard subgroup class. -/
def conclusion_s4_hodge_recovers_standard_quotient_genera_four_cycle_count :
    conclusion_s4_hodge_recovers_standard_quotient_genera_subgroup → ℕ
  | .tau => 0
  | .delta => 0
  | .sigma3 => 0
  | .sigma4 => 2
  | .v4 => 0
  | .s3 => 0
  | .d8 => 2
  | .a4 => 0
  | .s4 => 6

/-- Identity value of the genus-`49` Hodge character. -/
def conclusion_s4_hodge_recovers_standard_quotient_genera_identity_character : ℤ := 49

/-- Character sum over a standard subgroup class. -/
def conclusion_s4_hodge_recovers_standard_quotient_genera_character_sum
    (H : conclusion_s4_hodge_recovers_standard_quotient_genera_subgroup) : ℤ :=
  conclusion_s4_hodge_recovers_standard_quotient_genera_identity_character +
    ((conclusion_s4_hodge_recovers_standard_quotient_genera_transposition_count H : ℕ) : ℤ) *
      conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character .transposition +
    ((conclusion_s4_hodge_recovers_standard_quotient_genera_double_transposition_count H : ℕ) : ℤ) *
      conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character .doubleTransposition +
    ((conclusion_s4_hodge_recovers_standard_quotient_genera_three_cycle_count H : ℕ) : ℤ) *
      conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character .threeCycle +
    ((conclusion_s4_hodge_recovers_standard_quotient_genera_four_cycle_count H : ℕ) : ℤ) *
      conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character .fourCycle

/-- Quotient genus recovered by character averaging. -/
def conclusion_s4_hodge_recovers_standard_quotient_genera_quotient_genus
    (H : conclusion_s4_hodge_recovers_standard_quotient_genera_subgroup) : ℚ :=
  conclusion_s4_hodge_recovers_standard_quotient_genera_character_sum H /
    conclusion_s4_hodge_recovers_standard_quotient_genera_order H

/-- Concrete conclusion package for the standard `S₄` quotient genera. -/
def conclusion_s4_hodge_recovers_standard_quotient_genera_statement : Prop :=
  conclusion_s4_hodge_determines_fixedpoint_counts_statement ∧
    conclusion_s4_hodge_recovers_standard_quotient_genera_quotient_genus .tau = 19 ∧
    conclusion_s4_hodge_recovers_standard_quotient_genera_quotient_genus .delta = 25 ∧
    conclusion_s4_hodge_recovers_standard_quotient_genera_quotient_genus .sigma3 = 17 ∧
    conclusion_s4_hodge_recovers_standard_quotient_genera_quotient_genus .sigma4 = 13 ∧
    conclusion_s4_hodge_recovers_standard_quotient_genera_quotient_genus .v4 = 13 ∧
    conclusion_s4_hodge_recovers_standard_quotient_genera_quotient_genus .s3 = 3 ∧
    conclusion_s4_hodge_recovers_standard_quotient_genera_quotient_genus .d8 = 4 ∧
    conclusion_s4_hodge_recovers_standard_quotient_genera_quotient_genus .a4 = 5 ∧
    conclusion_s4_hodge_recovers_standard_quotient_genera_quotient_genus .s4 = 0

/-- Paper label: `thm:conclusion-s4-hodge-recovers-standard-quotient-genera`. -/
theorem paper_conclusion_s4_hodge_recovers_standard_quotient_genera :
    conclusion_s4_hodge_recovers_standard_quotient_genera_statement := by
  refine ⟨paper_conclusion_s4_hodge_determines_fixedpoint_counts, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    norm_num [conclusion_s4_hodge_recovers_standard_quotient_genera_quotient_genus,
      conclusion_s4_hodge_recovers_standard_quotient_genera_character_sum,
      conclusion_s4_hodge_recovers_standard_quotient_genera_identity_character,
      conclusion_s4_hodge_recovers_standard_quotient_genera_order,
      conclusion_s4_hodge_recovers_standard_quotient_genera_transposition_count,
      conclusion_s4_hodge_recovers_standard_quotient_genera_double_transposition_count,
      conclusion_s4_hodge_recovers_standard_quotient_genera_three_cycle_count,
      conclusion_s4_hodge_recovers_standard_quotient_genera_four_cycle_count,
      conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character]

end Omega.Conclusion
