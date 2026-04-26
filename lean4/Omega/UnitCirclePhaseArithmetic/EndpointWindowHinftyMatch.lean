import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.RamanujanCollapse

namespace Omega.UnitCirclePhaseArithmetic

/-- The small boundary-layer parameter in the off-critical shift estimate. -/
noncomputable def app_jensen_offcritical_shift_boundary_q (γ r0 : ℝ) : ℝ :=
  ((1 - r0 ^ 2) ^ 2 / (1 + r0 ^ 2) ^ 2) * (γ ^ 2 + 1)

/-- The closed-form boundary-layer upper bound `Δ(γ; r₀)`. -/
noncomputable def app_jensen_offcritical_shift_boundary_delta (γ r0 : ℝ) : ℝ :=
  ((1 + r0 ^ 2) / (1 - r0 ^ 2)) *
    (1 - Real.sqrt (1 - app_jensen_offcritical_shift_boundary_q γ r0))

/-- The endpoint-window `h_\infty` rate written in the golden-ratio base. -/
noncomputable def endpointHinftyRate : ℝ :=
  Real.log (2 / Real.sqrt Real.goldenRatio) / Real.log Real.goldenRatio

/-- Concrete endpoint-window asymptotic data under the scaling
`Y_m = (4 / φ^2)^m`, `η_m = c * φ^{-m}`, with explicit closed forms for the window and
probability scales. -/
structure EndpointWindowHinftyMatchData where
  m : ℕ
  c : ℝ
  Ym : ℝ
  eta : ℝ
  windowMass : ℝ
  probabilityMass : ℝ
  hYm : Ym = (4 / Real.goldenRatio ^ 2) ^ m
  heta : eta = c * (Real.goldenRatio⁻¹) ^ m
  hwindow : windowMass = c * (2 / Real.sqrt Real.goldenRatio) ^ m
  hprobability : probabilityMass = c * (2 / Real.sqrt Real.goldenRatio) ^ m

namespace EndpointWindowHinftyMatchData

/-- The endpoint angle-window scale matches the `h_\infty` exponential rate. -/
def windowExponentialMatch (D : EndpointWindowHinftyMatchData) : Prop :=
  D.windowMass = D.c * Real.goldenRatio ^ (endpointHinftyRate * (D.m : ℝ))

/-- The corresponding endpoint probability scale matches the same `h_\infty` exponential rate. -/
def probabilityExponentialMatch (D : EndpointWindowHinftyMatchData) : Prop :=
  D.probabilityMass = D.c * Real.goldenRatio ^ (endpointHinftyRate * (D.m : ℝ))

private lemma endpoint_base_eq_hinfty_rate :
    (2 / Real.sqrt Real.goldenRatio : ℝ) = Real.goldenRatio ^ endpointHinftyRate := by
  have hφ_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hbase_pos : 0 < (2 / Real.sqrt Real.goldenRatio : ℝ) := by
    positivity
  have hlog_ne : Real.log Real.goldenRatio ≠ 0 := by
    exact ne_of_gt (Real.log_pos Real.one_lt_goldenRatio)
  calc
    (2 / Real.sqrt Real.goldenRatio : ℝ) = Real.exp (Real.log (2 / Real.sqrt Real.goldenRatio)) := by
      rw [Real.exp_log hbase_pos]
    _ = Real.exp (Real.log Real.goldenRatio * endpointHinftyRate) := by
      congr 1
      unfold endpointHinftyRate
      field_simp [hlog_ne]
    _ = Real.goldenRatio ^ endpointHinftyRate := by
      rw [Real.rpow_def_of_pos hφ_pos]

private lemma endpoint_scale_eq_rate (m : ℕ) :
    (2 / Real.sqrt Real.goldenRatio : ℝ) ^ m =
      Real.goldenRatio ^ (endpointHinftyRate * (m : ℝ)) := by
  calc
    (2 / Real.sqrt Real.goldenRatio : ℝ) ^ m =
        ((2 / Real.sqrt Real.goldenRatio : ℝ) ^ (m : ℝ)) := by
          symm
          exact Real.rpow_natCast _ m
    _ = (Real.goldenRatio ^ endpointHinftyRate) ^ (m : ℝ) := by
          rw [endpoint_base_eq_hinfty_rate]
    _ = Real.goldenRatio ^ (endpointHinftyRate * (m : ℝ)) := by
          rw [Real.rpow_mul (le_of_lt Real.goldenRatio_pos)]

lemma windowExponentialMatch_proof (D : EndpointWindowHinftyMatchData) : D.windowExponentialMatch := by
  unfold windowExponentialMatch
  rw [D.hwindow, endpoint_scale_eq_rate]

lemma probabilityExponentialMatch_proof (D : EndpointWindowHinftyMatchData) :
    D.probabilityExponentialMatch := by
  unfold probabilityExponentialMatch
  rw [D.hprobability, endpoint_scale_eq_rate]

end EndpointWindowHinftyMatchData

open EndpointWindowHinftyMatchData

/-- Under the standard endpoint scaling, both the angle-window measure and the endpoint
probability inherit the same golden-ratio `h_\infty` exponential rate.
    thm:app-endpoint-window-hinfty-match -/
theorem paper_app_endpoint_window_hinfty_match (D : EndpointWindowHinftyMatchData) :
    D.windowExponentialMatch ∧ D.probabilityExponentialMatch := by
  exact ⟨D.windowExponentialMatch_proof, D.probabilityExponentialMatch_proof⟩

/-- Paper label: `cor:app-jensen-offcritical-shift-boundary`.
After rewriting `1 - sqrt (1 - q)` as `q / (1 + sqrt (1 - q))`, the boundary-layer correction is
the first-order term times the explicit factor `2 / (1 + sqrt (1 - q))`. -/
theorem paper_app_jensen_offcritical_shift_boundary (γ r0 : ℝ)
    (hr0 : r0 ^ 2 ≠ 1) (hq : app_jensen_offcritical_shift_boundary_q γ r0 ≤ 1) :
    app_jensen_offcritical_shift_boundary_delta γ r0 =
      ((γ ^ 2 + 1) / 2) * ((1 - r0 ^ 2) / (1 + r0 ^ 2)) *
        (2 / (1 + Real.sqrt (1 - app_jensen_offcritical_shift_boundary_q γ r0))) := by
  let q := app_jensen_offcritical_shift_boundary_q γ r0
  have hq_nonneg : 0 ≤ q := by
    dsimp [q, app_jensen_offcritical_shift_boundary_q]
    positivity
  have hsqrt :
      1 - Real.sqrt (1 - q) = q / (1 + Real.sqrt (1 - q)) := by
    have h1q_nonneg : 0 ≤ 1 - q := sub_nonneg.mpr hq
    have hden : 1 + Real.sqrt (1 - q) ≠ 0 := by
      positivity
    apply (eq_div_iff hden).2
    nlinarith [Real.sq_sqrt h1q_nonneg]
  have hplus_ne : 1 + r0 ^ 2 ≠ 0 := by positivity
  have hminus_ne : 1 - r0 ^ 2 ≠ 0 := by
    exact sub_ne_zero.mpr hr0.symm
  have hroot_den :
      1 + Real.sqrt (1 - app_jensen_offcritical_shift_boundary_q γ r0) ≠ 0 := by
    positivity
  unfold app_jensen_offcritical_shift_boundary_delta
  rw [show
      1 - Real.sqrt (1 - app_jensen_offcritical_shift_boundary_q γ r0) =
        app_jensen_offcritical_shift_boundary_q γ r0 /
          (1 + Real.sqrt (1 - app_jensen_offcritical_shift_boundary_q γ r0)) by
        simpa [q] using hsqrt]
  unfold app_jensen_offcritical_shift_boundary_q
  field_simp [hplus_ne, hminus_ne, hroot_den]

end Omega.UnitCirclePhaseArithmetic
