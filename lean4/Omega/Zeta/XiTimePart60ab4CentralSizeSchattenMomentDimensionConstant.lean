import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Zeta.XiTimePart60ab4CentralSizeOperatorTwoTraceSpectralIdentification
import Omega.Zeta.XiTimePart60ab4ExactSizebiasPushforwardLaw
import Omega.Zeta.XiTimePart60ab4UniformFiberSpectrumTwoatomMomentClosure

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete wrapper for the central-size moment package. It carries the previously verified
uniform two-atom moment seed and exact size-bias seed, together with a finite spectral model whose
weighted trace is normalized by the two-trace identification theorem. -/
structure xi_time_part60ab4_central_size_schatten_moment_dimension_constant_data where
  uniformSeed : xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_data
  traceIndex : Type
  traceFintype : Fintype traceIndex
  traceSize : traceIndex → ℝ
  traceObservable : ℝ → ℝ
  traceDenominator_ne : (∑ i, traceSize i) ≠ 0

namespace xi_time_part60ab4_central_size_schatten_moment_dimension_constant_data

/-- The exact size-biased first moment of the audited window-`6` fiber size. -/
def xi_time_part60ab4_central_size_schatten_moment_dimension_constant_regular_moment :
    ℚ :=
  xi_time_part60ab4_exact_sizebias_pushforward_law_microstate_pushforward_expectation
    (fun d => d)

/-- A centered quadratic audit moment around the visible center `3`. -/
def xi_time_part60ab4_central_size_schatten_moment_dimension_constant_center_moment :
    ℚ :=
  xi_time_part60ab4_exact_sizebias_pushforward_law_microstate_pushforward_expectation
    (fun d => ((d : ℚ) - 3) ^ (2 : ℕ))

/-- The `q = 1` main coefficient inherited from the two-atom uniform moment package. -/
def xi_time_part60ab4_central_size_schatten_moment_dimension_constant_q_one_constant :
    ℝ :=
  ((Real.goldenRatio : ℝ) + (Real.goldenRatio⁻¹) ^ (1 : ℕ)) / Real.sqrt 5

/-- The window-`6` groupoid/Wedderburn dimension constant
`8 * 2^2 + 4 * 3^2 + 9 * 4^2`. -/
def xi_time_part60ab4_central_size_schatten_moment_dimension_constant_dimension_main :
    ℕ :=
  8 * 2 ^ (2 : ℕ) + 4 * 3 ^ (2 : ℕ) + 9 * 4 ^ (2 : ℕ)

/-- The two-trace normalized spectral identity for the finite central-size model carried by `D`. -/
def xi_time_part60ab4_central_size_schatten_moment_dimension_constant_spectral_trace
    (D : xi_time_part60ab4_central_size_schatten_moment_dimension_constant_data) : Prop :=
  let _ := D.traceFintype
  (∑ i, D.traceSize i * D.traceObservable (D.traceSize i)) / (∑ i, D.traceSize i) =
    ((∑ i, D.traceSize i * D.traceObservable (D.traceSize i)) / Fintype.card D.traceIndex) /
      ((∑ i, D.traceSize i) / Fintype.card D.traceIndex)

/-- Paper-facing statement: existing uniform and exact size-bias packages, the normalized
two-trace spectral identity, the audited first and centered moments, the `q = 1` coefficient, and
the finite Wedderburn dimension constant. -/
def statement
    (D : xi_time_part60ab4_central_size_schatten_moment_dimension_constant_data) : Prop :=
  D.uniformSeed.statement ∧
    xi_time_part60ab4_exact_sizebias_pushforward_law_statement D.uniformSeed.pushforwardSeed ∧
    D.xi_time_part60ab4_central_size_schatten_moment_dimension_constant_spectral_trace ∧
    xi_time_part60ab4_central_size_schatten_moment_dimension_constant_regular_moment = 53 / 16 ∧
    xi_time_part60ab4_central_size_schatten_moment_dimension_constant_center_moment = 13 / 16 ∧
    xi_time_part60ab4_central_size_schatten_moment_dimension_constant_q_one_constant =
      ((Real.goldenRatio : ℝ) + (Real.goldenRatio⁻¹) ^ (1 : ℕ)) / Real.sqrt 5 ∧
    xi_time_part60ab4_central_size_schatten_moment_dimension_constant_dimension_main = 212

end xi_time_part60ab4_central_size_schatten_moment_dimension_constant_data

open xi_time_part60ab4_central_size_schatten_moment_dimension_constant_data

/-- Paper label:
`thm:xi-time-part60ab4-central-size-schatten-moment-dimension-constant`. -/
theorem paper_xi_time_part60ab4_central_size_schatten_moment_dimension_constant
    (D : xi_time_part60ab4_central_size_schatten_moment_dimension_constant_data) : D.statement := by
  let _ := D.traceFintype
  have huniform := paper_xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure
    D.uniformSeed
  have hpush := paper_xi_time_part60ab4_exact_sizebias_pushforward_law
    D.uniformSeed.pushforwardSeed
  have htrace :
      D.xi_time_part60ab4_central_size_schatten_moment_dimension_constant_spectral_trace := by
    simpa [xi_time_part60ab4_central_size_schatten_moment_dimension_constant_spectral_trace] using
      paper_xi_time_part60ab4_central_size_operator_two_trace_spectral_identification
        D.traceSize D.traceObservable D.traceDenominator_ne
  refine ⟨huniform, hpush, htrace, ?_, ?_, rfl, ?_⟩
  · unfold xi_time_part60ab4_central_size_schatten_moment_dimension_constant_regular_moment
    unfold xi_time_part60ab4_exact_sizebias_pushforward_law_microstate_pushforward_expectation
    norm_num
  · unfold xi_time_part60ab4_central_size_schatten_moment_dimension_constant_center_moment
    unfold xi_time_part60ab4_exact_sizebias_pushforward_law_microstate_pushforward_expectation
    norm_num
  · unfold xi_time_part60ab4_central_size_schatten_moment_dimension_constant_dimension_main
    norm_num

end

end Omega.Zeta
