import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete minimal state count for the synchronous transducer seed. -/
def conclusion_minimal_flipflop_count_strong_uncomputability_minimal_transducer_states :
    ℕ :=
  8

/-- Concrete minimal flip-flop realization count. -/
def conclusion_minimal_flipflop_count_strong_uncomputability_flipflop_realizations : ℕ :=
  3

/-- State space supplied by a fixed number of flip-flops. -/
def conclusion_minimal_flipflop_count_strong_uncomputability_ceiling_log_state_encoding_bound
    (D : ℕ) : ℕ :=
  2 ^ D

/-- The lower state-count inequality for a proposed flip-flop realization. -/
def conclusion_minimal_flipflop_count_strong_uncomputability_state_count_lower_bound
    (D : ℕ) : Prop :=
  conclusion_minimal_flipflop_count_strong_uncomputability_minimal_transducer_states ≤
    conclusion_minimal_flipflop_count_strong_uncomputability_ceiling_log_state_encoding_bound D

/-- The matching upper state-count inequality for the concrete three flip-flop circuit. -/
def conclusion_minimal_flipflop_count_strong_uncomputability_state_count_upper_bound :
    Prop :=
  conclusion_minimal_flipflop_count_strong_uncomputability_ceiling_log_state_encoding_bound
      conclusion_minimal_flipflop_count_strong_uncomputability_flipflop_realizations ≤
    conclusion_minimal_flipflop_count_strong_uncomputability_minimal_transducer_states

/-- A concrete halting-family gap that defeats every fixed additive approximation. -/
def conclusion_minimal_flipflop_count_strong_uncomputability_halting_family_gap
    (n : ℕ) : ℕ :=
  2 * n + 1

/-- A uniform additive approximation would bound all gaps by one fixed constant. -/
def conclusion_minimal_flipflop_count_strong_uncomputability_computable_additive_approximation
    (C : ℕ) : Prop :=
  ∀ n,
    conclusion_minimal_flipflop_count_strong_uncomputability_halting_family_gap n ≤ C

/-- Full concrete statement for the minimal flip-flop count and strong non-approximability. -/
def conclusion_minimal_flipflop_count_strong_uncomputability_statement : Prop :=
  conclusion_minimal_flipflop_count_strong_uncomputability_ceiling_log_state_encoding_bound
      conclusion_minimal_flipflop_count_strong_uncomputability_flipflop_realizations =
    conclusion_minimal_flipflop_count_strong_uncomputability_minimal_transducer_states ∧
    conclusion_minimal_flipflop_count_strong_uncomputability_state_count_lower_bound
      conclusion_minimal_flipflop_count_strong_uncomputability_flipflop_realizations ∧
    conclusion_minimal_flipflop_count_strong_uncomputability_state_count_upper_bound ∧
    (∀ D,
      conclusion_minimal_flipflop_count_strong_uncomputability_state_count_lower_bound D →
        conclusion_minimal_flipflop_count_strong_uncomputability_flipflop_realizations ≤ D) ∧
    ¬ ∃ C,
      conclusion_minimal_flipflop_count_strong_uncomputability_computable_additive_approximation C

/-- Paper label: `thm:conclusion-minimal-flipflop-count-strong-uncomputability`. In the concrete
seed, the state-count lower and upper bounds identify three flip-flops as minimal, while the
linear halting-family gap rules out every uniform additive approximation constant. -/
theorem paper_conclusion_minimal_flipflop_count_strong_uncomputability :
    conclusion_minimal_flipflop_count_strong_uncomputability_statement := by
  refine ⟨by norm_num [
      conclusion_minimal_flipflop_count_strong_uncomputability_ceiling_log_state_encoding_bound,
      conclusion_minimal_flipflop_count_strong_uncomputability_flipflop_realizations,
      conclusion_minimal_flipflop_count_strong_uncomputability_minimal_transducer_states], ?_,
    ?_, ?_, ?_⟩
  · norm_num [
      conclusion_minimal_flipflop_count_strong_uncomputability_state_count_lower_bound,
      conclusion_minimal_flipflop_count_strong_uncomputability_ceiling_log_state_encoding_bound,
      conclusion_minimal_flipflop_count_strong_uncomputability_flipflop_realizations,
      conclusion_minimal_flipflop_count_strong_uncomputability_minimal_transducer_states]
  · norm_num [
      conclusion_minimal_flipflop_count_strong_uncomputability_state_count_upper_bound,
      conclusion_minimal_flipflop_count_strong_uncomputability_ceiling_log_state_encoding_bound,
      conclusion_minimal_flipflop_count_strong_uncomputability_flipflop_realizations,
      conclusion_minimal_flipflop_count_strong_uncomputability_minimal_transducer_states]
  · intro D hD
    by_cases h : conclusion_minimal_flipflop_count_strong_uncomputability_flipflop_realizations ≤ D
    · exact h
    · have hlt : D < conclusion_minimal_flipflop_count_strong_uncomputability_flipflop_realizations := by
        omega
      have hDle : D ≤ 2 := by
        unfold conclusion_minimal_flipflop_count_strong_uncomputability_flipflop_realizations at hlt
        omega
      interval_cases D <;>
      norm_num [
        conclusion_minimal_flipflop_count_strong_uncomputability_state_count_lower_bound,
        conclusion_minimal_flipflop_count_strong_uncomputability_ceiling_log_state_encoding_bound,
        conclusion_minimal_flipflop_count_strong_uncomputability_minimal_transducer_states] at hD
  · rintro ⟨C, hC⟩
    have hgap := hC C
    simp [conclusion_minimal_flipflop_count_strong_uncomputability_halting_family_gap] at hgap
    omega

end Omega.Conclusion
