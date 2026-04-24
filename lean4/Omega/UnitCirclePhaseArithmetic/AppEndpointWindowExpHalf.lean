import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppLegendreMomentTimefiber

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The endpoint window factor after the hyperbolic substitution. -/
def app_endpoint_window_exp_half_window_factor (ρ : ℝ) : ℝ :=
  1 - ρ

/-- The corresponding endpoint probability scale. -/
def app_endpoint_window_exp_half_probability_scale (ρ : ℝ) : ℝ :=
  Real.sqrt (1 - ρ)

/-- Exact `e^{-Y/2}` rewrite of the endpoint window/probability factors after substituting
`Y = 2 artanh(ρ)`. -/
def AppEndpointWindowExpHalfStatement (Y ρ : ℝ) : Prop :=
  Y = endpointLegendreRadius ρ →
    app_endpoint_window_exp_half_window_factor ρ = 2 / (Real.exp Y + 1) ∧
      app_endpoint_window_exp_half_probability_scale ρ =
        Real.sqrt 2 * Real.exp (-Y / 2) / Real.sqrt (1 + Real.exp (-Y)) ∧
      app_endpoint_window_exp_half_probability_scale ρ ≤
        Real.sqrt 2 * Real.exp (-Y / 2)

private lemma app_endpoint_window_exp_half_window_factor_formula
    (Y ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hYdef : Y = endpointLegendreRadius ρ) :
    app_endpoint_window_exp_half_window_factor ρ = 2 / (Real.exp Y + 1) := by
  have hρmem : ρ ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · linarith
    · exact hρ1
  have hhalf : Y / 2 = Real.artanh ρ := by
    rw [hYdef, endpointLegendreRadius]
    ring
  have hexp : Real.exp Y = (1 + ρ) / (1 - ρ) := by
    calc
      Real.exp Y = Real.exp (Y / 2 + Y / 2) := by congr 1; ring
      _ = Real.exp (Y / 2) * Real.exp (Y / 2) := by rw [Real.exp_add]
      _ = Real.sqrt ((1 + ρ) / (1 - ρ)) * Real.sqrt ((1 + ρ) / (1 - ρ)) := by
            rw [hhalf, Real.exp_artanh hρmem]
      _ = (1 + ρ) / (1 - ρ) := by
            exact Real.mul_self_sqrt (by
              have hnum : 0 ≤ 1 + ρ := by linarith
              have hden : 0 ≤ 1 - ρ := by linarith
              exact div_nonneg hnum hden)
  have hden : 1 - ρ ≠ 0 := by linarith
  apply (eq_div_iff (show Real.exp Y + 1 ≠ 0 by positivity)).2
  rw [hexp]
  unfold app_endpoint_window_exp_half_window_factor
  field_simp [hden]
  ring

private lemma app_endpoint_window_exp_half_probability_scale_formula
    (Y ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hYdef : Y = endpointLegendreRadius ρ) :
    app_endpoint_window_exp_half_probability_scale ρ =
      Real.sqrt 2 * Real.exp (-Y / 2) / Real.sqrt (1 + Real.exp (-Y)) := by
  have hwindow :=
    app_endpoint_window_exp_half_window_factor_formula Y ρ hρ0 hρ1 hYdef
  have hexp_ne : Real.exp Y ≠ 0 := by positivity
  have hsqrt_exp :
      Real.sqrt (Real.exp (-Y)) = Real.exp (-Y / 2) := by
    calc
      Real.sqrt (Real.exp (-Y)) = Real.sqrt ((Real.exp (-Y / 2)) ^ 2) := by
        congr 1
        rw [show -Y = (-Y / 2) + (-Y / 2) by ring, Real.exp_add]
        ring
      _ = Real.exp (-Y / 2) := by
        rw [Real.sqrt_sq]
        positivity
  calc
    app_endpoint_window_exp_half_probability_scale ρ = Real.sqrt (2 / (Real.exp Y + 1)) := by
      change Real.sqrt (app_endpoint_window_exp_half_window_factor ρ) = _
      rw [hwindow]
    _ = Real.sqrt (2 * Real.exp (-Y) / (1 + Real.exp (-Y))) := by
      congr 1
      rw [Real.exp_neg]
      field_simp [hexp_ne]
    _ = Real.sqrt (2 * Real.exp (-Y)) / Real.sqrt (1 + Real.exp (-Y)) := by
      rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-Y))]
    _ = Real.sqrt 2 * Real.sqrt (Real.exp (-Y)) / Real.sqrt (1 + Real.exp (-Y)) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
    _ = Real.sqrt 2 * Real.exp (-Y / 2) / Real.sqrt (1 + Real.exp (-Y)) := by
      rw [hsqrt_exp]

private lemma app_endpoint_window_exp_half_probability_scale_bound
    (Y ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (_hY : 0 < Y) (hYdef : Y = endpointLegendreRadius ρ) :
    app_endpoint_window_exp_half_probability_scale ρ ≤ Real.sqrt 2 * Real.exp (-Y / 2) := by
  rw [app_endpoint_window_exp_half_probability_scale_formula Y ρ hρ0 hρ1 hYdef]
  set a : ℝ := Real.sqrt 2 * Real.exp (-Y / 2)
  set d : ℝ := Real.sqrt (1 + Real.exp (-Y))
  have ha_nonneg : 0 ≤ a := by
    unfold a
    positivity
  have hd_pos : 0 < d := by
    unfold d
    apply Real.sqrt_pos.2
    positivity
  have hd_ge_one : 1 ≤ d := by
    unfold d
    have hinner : 1 ≤ 1 + Real.exp (-Y) := by
      have hexp_pos : 0 < Real.exp (-Y) := Real.exp_pos (-Y)
      nlinarith
    exact (Real.one_le_sqrt).2 hinner
  have hdiv : a / d ≤ a / 1 := by
    simpa using div_le_div_of_nonneg_left ha_nonneg (by norm_num : (0 : ℝ) < 1) hd_ge_one
  simpa [a] using hdiv

/-- Paper label: `cor:app-endpoint-window-exp-half`. -/
theorem paper_app_endpoint_window_exp_half
    (Y ρ : ℝ) (hY : 0 < Y) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    AppEndpointWindowExpHalfStatement Y ρ := by
  intro hYdef
  exact ⟨app_endpoint_window_exp_half_window_factor_formula Y ρ hρ0 hρ1 hYdef,
    app_endpoint_window_exp_half_probability_scale_formula Y ρ hρ0 hρ1 hYdef,
    app_endpoint_window_exp_half_probability_scale_bound Y ρ hρ0 hρ1 hY hYdef⟩

end

end Omega.UnitCirclePhaseArithmetic
