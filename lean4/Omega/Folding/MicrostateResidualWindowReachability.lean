import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Folding

open Real Finset

variable {X : Type*} [Fintype X]

/-- The inverse-window length `W_inv(π) = Σ_x π(x) log d(x)`.
    thm:fold-microstate-residual-window-reachability -/
noncomputable def residualWindow (pi : X → ℝ) (d : X → ℕ) : ℝ :=
  ∑ x, pi x * Real.log (d x : ℝ)

/-- The residual window is nonnegative when the macro weights are nonnegative and every fiber has
    positive size. `thm:fold-microstate-residual-window-reachability` -/
theorem residualWindow_nonneg (pi : X → ℝ) (d : X → ℕ)
    (hpi_nonneg : ∀ x, 0 ≤ pi x) (hd : ∀ x, 0 < d x) :
    0 ≤ residualWindow pi d := by
  unfold residualWindow
  refine Finset.sum_nonneg ?_
  intro x hx
  have hlog_nonneg : 0 ≤ Real.log (d x : ℝ) := by
    have hx' : (1 : ℝ) ≤ (d x : ℝ) := by exact_mod_cast hd x
    exact Real.log_nonneg hx'
  exact mul_nonneg (hpi_nonneg x) hlog_nonneg

/-- Paper package: every parameter `t ∈ [0,1]` determines a fiberwise residual profile
    `t · log d(x)`, whose weighted sum reaches the corresponding point `t · W_inv(π)` of the full
    residual window; equivalently the associated entropy level lies in the closed interval
    `[H(π), H(π) + W_inv(π)]`.
    thm:fold-microstate-residual-window-reachability -/
theorem paper_fold_microstate_residual_window_reachability
    (pi : X → ℝ) (d : X → ℕ) (Hpi : ℝ) (hpi_nonneg : ∀ x, 0 ≤ pi x)
    (_hpi_sum : ∑ x, pi x = 1) (hd : ∀ x, 0 < d x) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∃ fiberResidual : X → ℝ,
        (∀ x, fiberResidual x = t * Real.log (d x : ℝ)) ∧
        (∀ x, 0 ≤ fiberResidual x ∧ fiberResidual x ≤ Real.log (d x : ℝ)) ∧
        (∑ x, pi x * fiberResidual x = t * residualWindow pi d) ∧
        (0 ≤ t * residualWindow pi d ∧ t * residualWindow pi d ≤ residualWindow pi d) ∧
        (Hpi + residualWindow pi d - t * residualWindow pi d =
          Hpi + (1 - t) * residualWindow pi d) ∧
        (Hpi ≤ Hpi + (1 - t) * residualWindow pi d ∧
          Hpi + (1 - t) * residualWindow pi d ≤ Hpi + residualWindow pi d) := by
  intro t ht0 ht1
  have hW_nonneg : 0 ≤ residualWindow pi d := residualWindow_nonneg pi d hpi_nonneg hd
  refine ⟨fun x => t * Real.log (d x : ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    have hlog_nonneg : 0 ≤ Real.log (d x : ℝ) := by
      have hx' : (1 : ℝ) ≤ (d x : ℝ) := by exact_mod_cast hd x
      exact Real.log_nonneg hx'
    constructor
    · exact mul_nonneg ht0 hlog_nonneg
    · calc
        t * Real.log (d x : ℝ) ≤ 1 * Real.log (d x : ℝ) := by
          gcongr
        _ = Real.log (d x : ℝ) := by ring
  · unfold residualWindow
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring
  · constructor
    · exact mul_nonneg ht0 hW_nonneg
    · calc
        t * residualWindow pi d ≤ 1 * residualWindow pi d := by
          gcongr
        _ = residualWindow pi d := by ring
  · ring
  · constructor
    · have hscale_nonneg : 0 ≤ (1 - t) * residualWindow pi d := by
        have h1t_nonneg : 0 ≤ 1 - t := by linarith
        exact mul_nonneg h1t_nonneg hW_nonneg
      linarith
    · have hscale_le : (1 - t) * residualWindow pi d ≤ residualWindow pi d := by
        calc
          (1 - t) * residualWindow pi d ≤ 1 * residualWindow pi d := by
            have h1t_nonneg : 0 ≤ 1 - t := by linarith
            have h1t_le : 1 - t ≤ 1 := by linarith
            gcongr
          _ = residualWindow pi d := by ring
      linarith

end Omega.Folding
