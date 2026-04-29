import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Wedderburn block sizes in the audited `m = 6` foldbin groupoid model. -/
def conclusion_foldbin_groupoid_regular_trace_escort_wedderburn_block_size : Fin 3 → ℕ :=
  fun i =>
    match i.1 with
    | 0 => 2
    | 1 => 3
    | _ => 4

/-- Multiplicity histogram for the audited `m = 6` foldbin groupoid model. -/
def conclusion_foldbin_groupoid_regular_trace_escort_m6_histogram : Fin 3 → ℕ :=
  fun i =>
    match i.1 with
    | 0 => 8
    | 1 => 4
    | _ => 9

/-- Left-regular trace denominator `Σ n_d d²`. -/
def conclusion_foldbin_groupoid_regular_trace_escort_regular_trace_denominator : ℕ :=
  ∑ i : Fin 3,
    conclusion_foldbin_groupoid_regular_trace_escort_m6_histogram i *
      conclusion_foldbin_groupoid_regular_trace_escort_wedderburn_block_size i ^ (2 : ℕ)

/-- Normalized left-regular trace weight of a Wedderburn block. -/
def conclusion_foldbin_groupoid_regular_trace_escort_regular_trace_weight (i : Fin 3) : ℚ :=
  (conclusion_foldbin_groupoid_regular_trace_escort_m6_histogram i *
        conclusion_foldbin_groupoid_regular_trace_escort_wedderburn_block_size i ^ (2 : ℕ) :
      ℚ) /
    conclusion_foldbin_groupoid_regular_trace_escort_regular_trace_denominator

/-- Escort denominator `Σ n_d d`, the total number of audited microstates. -/
def conclusion_foldbin_groupoid_regular_trace_escort_escort_denominator : ℕ :=
  ∑ i : Fin 3,
    conclusion_foldbin_groupoid_regular_trace_escort_m6_histogram i *
      conclusion_foldbin_groupoid_regular_trace_escort_wedderburn_block_size i

/-- Escort weight obtained by size-biasing the `m = 6` block histogram. -/
def conclusion_foldbin_groupoid_regular_trace_escort_escort_weight (i : Fin 3) : ℚ :=
  (conclusion_foldbin_groupoid_regular_trace_escort_m6_histogram i *
      conclusion_foldbin_groupoid_regular_trace_escort_wedderburn_block_size i : ℚ) /
    conclusion_foldbin_groupoid_regular_trace_escort_escort_denominator

/-- Concrete finite statement for normalized regular trace and escort weights. -/
def conclusion_foldbin_groupoid_regular_trace_escort_statement : Prop :=
  conclusion_foldbin_groupoid_regular_trace_escort_regular_trace_denominator = 212 ∧
    (∑ i : Fin 3,
      conclusion_foldbin_groupoid_regular_trace_escort_regular_trace_weight i) = 1 ∧
    conclusion_foldbin_groupoid_regular_trace_escort_regular_trace_weight 0 = 8 / 53 ∧
    conclusion_foldbin_groupoid_regular_trace_escort_regular_trace_weight 1 = 9 / 53 ∧
    conclusion_foldbin_groupoid_regular_trace_escort_regular_trace_weight 2 = 36 / 53 ∧
    conclusion_foldbin_groupoid_regular_trace_escort_escort_denominator = 64 ∧
    (∑ i : Fin 3, conclusion_foldbin_groupoid_regular_trace_escort_escort_weight i) = 1 ∧
    conclusion_foldbin_groupoid_regular_trace_escort_escort_weight 0 = 1 / 4 ∧
    conclusion_foldbin_groupoid_regular_trace_escort_escort_weight 1 = 3 / 16 ∧
    conclusion_foldbin_groupoid_regular_trace_escort_escort_weight 2 = 9 / 16 ∧
    (∑ i : Fin 3,
      conclusion_foldbin_groupoid_regular_trace_escort_m6_histogram i) = 21

/-- Paper label: `thm:conclusion-foldbin-groupoid-regular-trace-escort`. -/
theorem paper_conclusion_foldbin_groupoid_regular_trace_escort :
    conclusion_foldbin_groupoid_regular_trace_escort_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [conclusion_foldbin_groupoid_regular_trace_escort_regular_trace_denominator,
      conclusion_foldbin_groupoid_regular_trace_escort_regular_trace_weight,
      conclusion_foldbin_groupoid_regular_trace_escort_escort_denominator,
      conclusion_foldbin_groupoid_regular_trace_escort_escort_weight,
      conclusion_foldbin_groupoid_regular_trace_escort_m6_histogram,
      conclusion_foldbin_groupoid_regular_trace_escort_wedderburn_block_size,
      Fin.sum_univ_three]

end Omega.Conclusion
