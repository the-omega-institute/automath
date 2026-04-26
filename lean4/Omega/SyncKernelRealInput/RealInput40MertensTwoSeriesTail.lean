import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.SyncKernelWeighted.RealInput40LogMTruncBound

namespace Omega.SyncKernelRealInput

open Omega.SyncKernelWeighted

noncomputable section

/-- Specialization of the appendix geometric-tail bound to the real-input-40 two-series constant.
The paper's `q = φ⁻²` corresponds to `λ = φ²`, and the combined logarithmic coefficients are
bounded by the single majorant constant `A = 5`. -/
def real_input_40_mertens_two_series_tail_statement (N : ℕ) : Prop :=
  (∀ n, realInput40LogMTruncTerm 5 (Real.goldenRatio ^ (2 : ℕ)) N n ≤
      realInput40LogMTruncMajorant 5 (Real.goldenRatio ^ (2 : ℕ)) N n) ∧
    (∑' n, realInput40LogMTruncTerm 5 (Real.goldenRatio ^ (2 : ℕ)) N n) ≤
      realInput40LogMTruncGeomBound 5 (Real.goldenRatio ^ (2 : ℕ)) N ∧
    realInput40LogMTruncGeomBound 5 (Real.goldenRatio ^ (2 : ℕ)) N =
      realInput40LogMTruncClosedBound 5 (Real.goldenRatio ^ (2 : ℕ)) N

theorem real_input_40_mertens_two_series_tail_true (N : ℕ) :
    real_input_40_mertens_two_series_tail_statement N := by
  have hA : (0 : ℝ) ≤ 5 := by norm_num
  have hlam : 1 < Real.goldenRatio ^ (2 : ℕ) := by
    nlinarith [Real.one_lt_goldenRatio]
  simpa [real_input_40_mertens_two_series_tail_statement] using
    paper_real_input_40_logM_trunc_bound 5 (Real.goldenRatio ^ (2 : ℕ)) N hA hlam

/-- Paper label: `cor:real-input-40-mertens-two-series-tail`. -/
def paper_real_input_40_mertens_two_series_tail (N : ℕ) : Prop := by
  exact real_input_40_mertens_two_series_tail_statement N

end

end Omega.SyncKernelRealInput
