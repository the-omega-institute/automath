import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.RamanujanCollapse

namespace Omega.UnitCirclePhaseArithmetic

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

end Omega.UnitCirclePhaseArithmetic
