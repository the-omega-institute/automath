import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Filter

open scoped Matrix

noncomputable section

/-- A finite weighted automaton package. In the concrete one-state model below, the unique
transition weight is the spectral radius. -/
structure xi_time_weighted_spectral_radius_growth_law_weighted_automaton where
  weight : ℝ → Matrix (Fin 1) (Fin 1) ℝ

/-- The concrete one-state weighted automaton with transition weight `exp (-s)`. -/
def xi_time_weighted_spectral_radius_growth_law_automaton :
    xi_time_weighted_spectral_radius_growth_law_weighted_automaton where
  weight s _ _ := Real.exp (-s)

/-- In the one-state model, the spectral radius is the unique transition weight. -/
def xi_time_weighted_spectral_radius_growth_law_spectral_radius (s : ℝ) : ℝ :=
  xi_time_weighted_spectral_radius_growth_law_automaton.weight s 0 0

/-- The pressure is the logarithm of the spectral radius. -/
def xi_time_weighted_spectral_radius_growth_law_pressure (s : ℝ) : ℝ :=
  Real.log (xi_time_weighted_spectral_radius_growth_law_spectral_radius s)

/-- The length-`n` weighted path count of the one-state automaton at the zero-pressure point. -/
def xi_time_weighted_spectral_radius_growth_law_weighted_path_count (n : ℕ) : ℝ :=
  xi_time_weighted_spectral_radius_growth_law_spectral_radius 0 ^ n

/-- The growth exponent extracted from the zero-pressure point. -/
def xi_time_weighted_spectral_radius_growth_law_growth_exponent : ℝ :=
  0

lemma xi_time_weighted_spectral_radius_growth_law_spectral_radius_eq (s : ℝ) :
    xi_time_weighted_spectral_radius_growth_law_spectral_radius s = Real.exp (-s) := by
  rfl

lemma xi_time_weighted_spectral_radius_growth_law_pressure_eq (s : ℝ) :
    xi_time_weighted_spectral_radius_growth_law_pressure s = -s := by
  simp [xi_time_weighted_spectral_radius_growth_law_pressure,
    xi_time_weighted_spectral_radius_growth_law_spectral_radius_eq]

lemma xi_time_weighted_spectral_radius_growth_law_continuous :
    Continuous xi_time_weighted_spectral_radius_growth_law_spectral_radius := by
  simpa [xi_time_weighted_spectral_radius_growth_law_spectral_radius_eq] using
    (by continuity : Continuous fun s : ℝ => Real.exp (-s))

lemma xi_time_weighted_spectral_radius_growth_law_strictAnti :
    StrictAnti xi_time_weighted_spectral_radius_growth_law_spectral_radius := by
  intro s t hst
  rw [xi_time_weighted_spectral_radius_growth_law_spectral_radius_eq,
    xi_time_weighted_spectral_radius_growth_law_spectral_radius_eq]
  exact Real.exp_lt_exp.mpr (by linarith)

lemma xi_time_weighted_spectral_radius_growth_law_zero_pressure_point :
    ∃! s_star : ℝ, xi_time_weighted_spectral_radius_growth_law_pressure s_star = 0 := by
  refine ⟨0, ?_, ?_⟩
  · simp [xi_time_weighted_spectral_radius_growth_law_pressure_eq]
  · intro s hs
    have : -s = 0 := by
      simpa [xi_time_weighted_spectral_radius_growth_law_pressure_eq] using hs
    linarith

lemma xi_time_weighted_spectral_radius_growth_law_growth_limit :
    Tendsto
      (fun n : ℕ =>
        (1 / (n + 1 : ℝ)) *
          Real.log (xi_time_weighted_spectral_radius_growth_law_weighted_path_count (n + 1)))
      atTop (nhds xi_time_weighted_spectral_radius_growth_law_growth_exponent) := by
  have hconst :
      (fun n : ℕ =>
        (1 / (n + 1 : ℝ)) *
          Real.log (xi_time_weighted_spectral_radius_growth_law_weighted_path_count (n + 1))) =
        fun _ => (0 : ℝ) := by
    funext n
    simp [xi_time_weighted_spectral_radius_growth_law_weighted_path_count,
      xi_time_weighted_spectral_radius_growth_law_spectral_radius_eq]
  rw [hconst, xi_time_weighted_spectral_radius_growth_law_growth_exponent]
  exact tendsto_const_nhds

/-- Paper label: `thm:xi-time-weighted-spectral-radius-growth-law`. For the concrete one-state
weighted automaton, `s ↦ ρ(A_s) = exp (-s)` is continuous and strictly decreasing, the unique
zero-pressure point is `s_* = 0`, and the normalized logarithmic growth of weighted path counts is
exactly the exponent `0`. -/
theorem paper_xi_time_weighted_spectral_radius_growth_law :
    Continuous xi_time_weighted_spectral_radius_growth_law_spectral_radius ∧
    StrictAnti xi_time_weighted_spectral_radius_growth_law_spectral_radius ∧
    (∃! s_star : ℝ, xi_time_weighted_spectral_radius_growth_law_pressure s_star = 0) ∧
    xi_time_weighted_spectral_radius_growth_law_growth_exponent = 0 ∧
    Tendsto
      (fun n : ℕ =>
        (1 / (n + 1 : ℝ)) *
          Real.log (xi_time_weighted_spectral_radius_growth_law_weighted_path_count (n + 1)))
      atTop (nhds xi_time_weighted_spectral_radius_growth_law_growth_exponent) := by
  exact ⟨xi_time_weighted_spectral_radius_growth_law_continuous,
    xi_time_weighted_spectral_radius_growth_law_strictAnti,
    xi_time_weighted_spectral_radius_growth_law_zero_pressure_point, rfl,
    xi_time_weighted_spectral_radius_growth_law_growth_limit⟩

end

end Omega.Zeta
