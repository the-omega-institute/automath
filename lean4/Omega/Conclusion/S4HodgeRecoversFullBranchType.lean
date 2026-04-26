import Mathlib.Tactic
import Omega.Conclusion.S4HodgeDeterminesFixedpointCounts

namespace Omega.Conclusion

/-- Riemann-Hurwitz input data for the genus-`49` regular `S₄` cover. -/
structure conclusion_s4_hodge_recovers_full_branch_type_data where
  curve_genus : ℕ
  quotient_genus : ℕ
  group_order : ℕ
  curve_genus_eq : curve_genus = 49
  quotient_genus_eq : quotient_genus = 0
  group_order_eq : group_order = 24

/-- Fixed-point count of each nontrivial `S₄` conjugacy class in the Hodge representation. -/
def conclusion_s4_hodge_recovers_full_branch_type_fixed_points
    (c : conclusion_s4_hodge_determines_fixedpoint_counts_conjugacy_class) : ℤ :=
  conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz c

/-- The Riemann-Hurwitz total ramification term for the regular cover. -/
def conclusion_s4_hodge_recovers_full_branch_type_total_ramification
    (D : conclusion_s4_hodge_recovers_full_branch_type_data) : ℤ :=
  (2 * (D.curve_genus : ℤ) - 2) -
    (D.group_order : ℤ) * (2 * (D.quotient_genus : ℤ) - 2)

/-- Contribution of one simple transposition branch value in an `S₄` regular cover. -/
def conclusion_s4_hodge_recovers_full_branch_type_transposition_contribution
    (D : conclusion_s4_hodge_recovers_full_branch_type_data) : ℤ :=
  (D.group_order : ℤ) / 2

/-- Branch-value count forced by the total ramification and transposition contribution. -/
def conclusion_s4_hodge_recovers_full_branch_type_simple_transposition_branch_values
    (D : conclusion_s4_hodge_recovers_full_branch_type_data) : ℤ :=
  conclusion_s4_hodge_recovers_full_branch_type_total_ramification D /
    conclusion_s4_hodge_recovers_full_branch_type_transposition_contribution D

/-- Concrete conclusion package for recovering the full branch type. -/
def conclusion_s4_hodge_recovers_full_branch_type_statement
    (D : conclusion_s4_hodge_recovers_full_branch_type_data) : Prop :=
  conclusion_s4_hodge_determines_fixedpoint_counts_statement ∧
    (∀ c : conclusion_s4_hodge_determines_fixedpoint_counts_conjugacy_class,
      conclusion_s4_hodge_recovers_full_branch_type_fixed_points c ≠ 0 → c = .transposition) ∧
      conclusion_s4_hodge_recovers_full_branch_type_total_ramification D = 144 ∧
        conclusion_s4_hodge_recovers_full_branch_type_transposition_contribution D = 12 ∧
          conclusion_s4_hodge_recovers_full_branch_type_simple_transposition_branch_values D = 12

/-- Paper label: `thm:conclusion-s4-hodge-recovers-full-branch-type`. -/
theorem paper_conclusion_s4_hodge_recovers_full_branch_type
    (D : conclusion_s4_hodge_recovers_full_branch_type_data) :
    conclusion_s4_hodge_recovers_full_branch_type_statement D := by
  refine ⟨paper_conclusion_s4_hodge_determines_fixedpoint_counts, ?_, ?_, ?_, ?_⟩
  · intro c hc
    cases c
    · rfl
    · exfalso
      norm_num [conclusion_s4_hodge_recovers_full_branch_type_fixed_points,
        conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz,
        conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character] at hc
    · exfalso
      norm_num [conclusion_s4_hodge_recovers_full_branch_type_fixed_points,
        conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz,
        conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character] at hc
    · exfalso
      norm_num [conclusion_s4_hodge_recovers_full_branch_type_fixed_points,
        conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz,
        conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character] at hc
  · rw [conclusion_s4_hodge_recovers_full_branch_type_total_ramification,
      D.curve_genus_eq, D.quotient_genus_eq, D.group_order_eq]
    norm_num
  · rw [conclusion_s4_hodge_recovers_full_branch_type_transposition_contribution,
      D.group_order_eq]
    norm_num
  · rw [conclusion_s4_hodge_recovers_full_branch_type_simple_transposition_branch_values,
      conclusion_s4_hodge_recovers_full_branch_type_total_ramification,
      conclusion_s4_hodge_recovers_full_branch_type_transposition_contribution,
      D.curve_genus_eq, D.quotient_genus_eq, D.group_order_eq]
    norm_num

end Omega.Conclusion
