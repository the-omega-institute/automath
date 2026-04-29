import Mathlib.Tactic
import Omega.Experiments.MarkovTVSampleComplexity

namespace Omega.Zeta

open Omega.Experiments.MarkovTVSampleComplexity

noncomputable section

/-- Concrete four-budget package for the prefix-readout audit. The data term is the same
Markov-TV envelope used elsewhere in the finite Chebotarev audit; the other three axes are the
deterministic time tail, fiber ambiguity, and the audited `NULL` gap. -/
structure prefix_readout_orthogonal_error_decomposition_data where
  prefix_readout_orthogonal_error_decomposition_tau : ℝ
  prefix_readout_orthogonal_error_decomposition_observed_error : ℝ
  prefix_readout_orthogonal_error_decomposition_time_tail : ℝ
  prefix_readout_orthogonal_error_decomposition_sample_count : ℝ
  prefix_readout_orthogonal_error_decomposition_state_count : ℝ
  prefix_readout_orthogonal_error_decomposition_delta_conf : ℝ
  prefix_readout_orthogonal_error_decomposition_gamma_ps : ℝ
  prefix_readout_orthogonal_error_decomposition_fiber_ambiguity : ℝ
  prefix_readout_orthogonal_error_decomposition_null_gap : ℝ
  prefix_readout_orthogonal_error_decomposition_h_four_budget :
    prefix_readout_orthogonal_error_decomposition_observed_error ≤
      prefix_readout_orthogonal_error_decomposition_time_tail +
        (prefix_readout_orthogonal_error_decomposition_state_count / 2) *
            markovTvEnvelopeRadius
              prefix_readout_orthogonal_error_decomposition_sample_count
              prefix_readout_orthogonal_error_decomposition_state_count
              prefix_readout_orthogonal_error_decomposition_delta_conf
              prefix_readout_orthogonal_error_decomposition_gamma_ps +
          prefix_readout_orthogonal_error_decomposition_fiber_ambiguity +
            prefix_readout_orthogonal_error_decomposition_null_gap
  prefix_readout_orthogonal_error_decomposition_h_time_budget :
    prefix_readout_orthogonal_error_decomposition_time_tail ≤
      prefix_readout_orthogonal_error_decomposition_tau / 3
  prefix_readout_orthogonal_error_decomposition_h_data_budget :
    (prefix_readout_orthogonal_error_decomposition_state_count / 2) *
        markovTvEnvelopeRadius
          prefix_readout_orthogonal_error_decomposition_sample_count
          prefix_readout_orthogonal_error_decomposition_state_count
          prefix_readout_orthogonal_error_decomposition_delta_conf
          prefix_readout_orthogonal_error_decomposition_gamma_ps ≤
      prefix_readout_orthogonal_error_decomposition_tau / 3
  prefix_readout_orthogonal_error_decomposition_h_fiber_budget :
    prefix_readout_orthogonal_error_decomposition_fiber_ambiguity ≤
      prefix_readout_orthogonal_error_decomposition_tau / 3
  prefix_readout_orthogonal_error_decomposition_h_null_budget :
    prefix_readout_orthogonal_error_decomposition_null_gap ≤ 0

namespace prefix_readout_orthogonal_error_decomposition_data

/-- The Markov-TV finite-data envelope term for the folded output histogram. -/
def prefix_readout_orthogonal_error_decomposition_data_envelope
    (D : prefix_readout_orthogonal_error_decomposition_data) : ℝ :=
  (D.prefix_readout_orthogonal_error_decomposition_state_count / 2) *
    markovTvEnvelopeRadius
      D.prefix_readout_orthogonal_error_decomposition_sample_count
      D.prefix_readout_orthogonal_error_decomposition_state_count
      D.prefix_readout_orthogonal_error_decomposition_delta_conf
      D.prefix_readout_orthogonal_error_decomposition_gamma_ps

/-- Sum of the four orthogonal audit budgets. -/
def prefix_readout_orthogonal_error_decomposition_four_budget
    (D : prefix_readout_orthogonal_error_decomposition_data) : ℝ :=
  D.prefix_readout_orthogonal_error_decomposition_time_tail +
    D.prefix_readout_orthogonal_error_decomposition_data_envelope +
      D.prefix_readout_orthogonal_error_decomposition_fiber_ambiguity +
        D.prefix_readout_orthogonal_error_decomposition_null_gap

end prefix_readout_orthogonal_error_decomposition_data

open prefix_readout_orthogonal_error_decomposition_data

/-- Concrete prefix-readout audit statement: the error is bounded by the orthogonal four-budget
sum, and the displayed `tau / 3` allocation plus a closed `NULL` gap gives total error at most
`tau`. -/
def prefix_readout_orthogonal_error_decomposition_statement
    (D : prefix_readout_orthogonal_error_decomposition_data) : Prop :=
  D.prefix_readout_orthogonal_error_decomposition_observed_error ≤
      D.prefix_readout_orthogonal_error_decomposition_four_budget ∧
    D.prefix_readout_orthogonal_error_decomposition_observed_error ≤
      D.prefix_readout_orthogonal_error_decomposition_tau

/-- Paper label: `thm:prefix-readout-orthogonal-error-decomposition`. Time tail, Markov-TV data
error, fiber ambiguity, and the audited `NULL` gap combine additively; allocating the first three
terms by thirds and closing the `NULL` term gives the advertised total prefix-readout bound. -/
theorem paper_prefix_readout_orthogonal_error_decomposition
    (D : prefix_readout_orthogonal_error_decomposition_data) :
    prefix_readout_orthogonal_error_decomposition_statement D := by
  refine ⟨?_, ?_⟩
  · simpa [prefix_readout_orthogonal_error_decomposition_four_budget,
      prefix_readout_orthogonal_error_decomposition_data_envelope] using
      D.prefix_readout_orthogonal_error_decomposition_h_four_budget
  · calc
      D.prefix_readout_orthogonal_error_decomposition_observed_error ≤
          D.prefix_readout_orthogonal_error_decomposition_time_tail +
            (D.prefix_readout_orthogonal_error_decomposition_state_count / 2) *
                markovTvEnvelopeRadius
                  D.prefix_readout_orthogonal_error_decomposition_sample_count
                  D.prefix_readout_orthogonal_error_decomposition_state_count
                  D.prefix_readout_orthogonal_error_decomposition_delta_conf
                  D.prefix_readout_orthogonal_error_decomposition_gamma_ps +
              D.prefix_readout_orthogonal_error_decomposition_fiber_ambiguity +
                D.prefix_readout_orthogonal_error_decomposition_null_gap :=
        D.prefix_readout_orthogonal_error_decomposition_h_four_budget
      _ ≤ D.prefix_readout_orthogonal_error_decomposition_tau / 3 +
            D.prefix_readout_orthogonal_error_decomposition_tau / 3 +
              D.prefix_readout_orthogonal_error_decomposition_tau / 3 + 0 := by
        linarith [D.prefix_readout_orthogonal_error_decomposition_h_time_budget,
          D.prefix_readout_orthogonal_error_decomposition_h_data_budget,
          D.prefix_readout_orthogonal_error_decomposition_h_fiber_budget,
          D.prefix_readout_orthogonal_error_decomposition_h_null_budget]
      _ = D.prefix_readout_orthogonal_error_decomposition_tau := by
        ring

end

end Omega.Zeta
