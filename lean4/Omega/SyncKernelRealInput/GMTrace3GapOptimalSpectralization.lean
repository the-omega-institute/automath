import Mathlib.Tactic
import Omega.SyncKernelWeighted.GMTrace3SpectralNormExtremal

namespace Omega.SyncKernelRealInput

open Omega.SyncKernelWeighted

/-- Concrete trace-gap package for the Guth--Maynard trace-`3` spectralization step. The
nonnegative displacement data are exactly the hypotheses needed by the sharp trace-`3` extremal
theorem. -/
structure gm_trace3_gap_optimal_spectralization_data where
  gm_trace3_gap_optimal_spectralization_m : ℕ
  gm_trace3_gap_optimal_spectralization_m_ge_two :
    2 ≤ gm_trace3_gap_optimal_spectralization_m
  gm_trace3_gap_optimal_spectralization_trace_sum : ℝ
  gm_trace3_gap_optimal_spectralization_trace_moment3 : ℝ
  gm_trace3_gap_optimal_spectralization_offset : ℝ
  gm_trace3_gap_optimal_spectralization_witness_offset : ℝ
  gm_trace3_gap_optimal_spectralization_trace_sum_nonneg :
    0 ≤ gm_trace3_gap_optimal_spectralization_trace_sum
  gm_trace3_gap_optimal_spectralization_offset_nonneg :
    0 ≤ gm_trace3_gap_optimal_spectralization_offset
  gm_trace3_gap_optimal_spectralization_offset_le_witness :
    gm_trace3_gap_optimal_spectralization_offset ≤
      gm_trace3_gap_optimal_spectralization_witness_offset

namespace gm_trace3_gap_optimal_spectralization_data

/-- The candidate top spectral value corresponding to the lower displacement. -/
noncomputable def spectral_point (D : gm_trace3_gap_optimal_spectralization_data) : ℝ :=
  D.gm_trace3_gap_optimal_spectralization_trace_sum /
      (D.gm_trace3_gap_optimal_spectralization_m : ℝ) +
    D.gm_trace3_gap_optimal_spectralization_offset

/-- The comparison spectral value corresponding to the larger displacement. -/
noncomputable def spectral_witness_point
    (D : gm_trace3_gap_optimal_spectralization_data) : ℝ :=
  D.gm_trace3_gap_optimal_spectralization_trace_sum /
      (D.gm_trace3_gap_optimal_spectralization_m : ℝ) +
    D.gm_trace3_gap_optimal_spectralization_witness_offset

/-- The two-point tail value forced by the trace-sum constraint. -/
noncomputable def two_point_tail (D : gm_trace3_gap_optimal_spectralization_data) : ℝ :=
  (D.gm_trace3_gap_optimal_spectralization_trace_sum - D.spectral_point) /
    (D.gm_trace3_gap_optimal_spectralization_m - 1 : ℝ)

/-- Jensen monotonicity makes the trace gap nonnegative along the admissible spectral ray. -/
def trace_gap_nonnegative (D : gm_trace3_gap_optimal_spectralization_data) : Prop :=
  gmTrace3LowerEnvelope D.gm_trace3_gap_optimal_spectralization_m
      D.gm_trace3_gap_optimal_spectralization_trace_sum D.spectral_point ≤
    gmTrace3LowerEnvelope D.gm_trace3_gap_optimal_spectralization_m
      D.gm_trace3_gap_optimal_spectralization_trace_sum D.spectral_witness_point

/-- The sharp spectral bound is the cubic equality after clearing the Jensen denominator. -/
def spectral_bound_optimal (D : gm_trace3_gap_optimal_spectralization_data) : Prop :=
  gmTrace3LowerEnvelope D.gm_trace3_gap_optimal_spectralization_m
      D.gm_trace3_gap_optimal_spectralization_trace_sum D.spectral_point =
        D.gm_trace3_gap_optimal_spectralization_trace_moment3 ↔
    gmTrace3Cubic D.gm_trace3_gap_optimal_spectralization_m
      D.gm_trace3_gap_optimal_spectralization_trace_sum
      D.gm_trace3_gap_optimal_spectralization_trace_moment3 D.spectral_point = 0

/-- The two-point spectrum saturates the trace sum and the Jensen lower envelope. -/
def two_point_spectrum_sharp (D : gm_trace3_gap_optimal_spectralization_data) : Prop :=
  D.spectral_point +
      (D.gm_trace3_gap_optimal_spectralization_m - 1 : ℝ) * D.two_point_tail =
        D.gm_trace3_gap_optimal_spectralization_trace_sum ∧
    D.spectral_point ^ 3 +
        (D.gm_trace3_gap_optimal_spectralization_m - 1 : ℝ) * D.two_point_tail ^ 3 =
      gmTrace3LowerEnvelope D.gm_trace3_gap_optimal_spectralization_m
        D.gm_trace3_gap_optimal_spectralization_trace_sum D.spectral_point

end gm_trace3_gap_optimal_spectralization_data

/-- Paper label: `prop:gm-trace3-gap-optimal-spectralization`. -/
theorem paper_gm_trace3_gap_optimal_spectralization
    (D : gm_trace3_gap_optimal_spectralization_data) :
    D.trace_gap_nonnegative ∧ D.spectral_bound_optimal ∧ D.two_point_spectrum_sharp := by
  simpa [gm_trace3_gap_optimal_spectralization_data.trace_gap_nonnegative,
    gm_trace3_gap_optimal_spectralization_data.spectral_bound_optimal,
    gm_trace3_gap_optimal_spectralization_data.two_point_spectrum_sharp,
    gm_trace3_gap_optimal_spectralization_data.spectral_point,
    gm_trace3_gap_optimal_spectralization_data.spectral_witness_point,
    gm_trace3_gap_optimal_spectralization_data.two_point_tail] using
    (Omega.SyncKernelWeighted.paper_gm_trace3_spectral_norm_extremal
      D.gm_trace3_gap_optimal_spectralization_m
      D.gm_trace3_gap_optimal_spectralization_m_ge_two
      (S1 := D.gm_trace3_gap_optimal_spectralization_trace_sum)
      (S3 := D.gm_trace3_gap_optimal_spectralization_trace_moment3)
      (u := D.gm_trace3_gap_optimal_spectralization_offset)
      (v := D.gm_trace3_gap_optimal_spectralization_witness_offset)
      D.gm_trace3_gap_optimal_spectralization_trace_sum_nonneg
      D.gm_trace3_gap_optimal_spectralization_offset_nonneg
      D.gm_trace3_gap_optimal_spectralization_offset_le_witness)

end Omega.SyncKernelRealInput
