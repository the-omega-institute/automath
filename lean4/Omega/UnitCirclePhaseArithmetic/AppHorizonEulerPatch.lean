import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The Möbius coordinate used in the Euler-patch disk chart. -/
def app_horizon_euler_patch_sigma (w : ℂ) : ℂ :=
  ((3 : ℂ) - w) / ((2 : ℂ) * (1 + w))

/-- Real-axis readout of the same Möbius coordinate. -/
def app_horizon_euler_patch_sigma_real (x : ℝ) : ℝ :=
  (3 - x) / (2 * (1 + x))

/-- A lightweight proxy for the Xi log-derivative in the Euler patch. -/
def app_horizon_euler_patch_xi_log_derivative (s : ℂ) : ℂ :=
  1 / (2 * s - 1)

/-- The `n`th absolutely convergent Euler-patch term. -/
def app_horizon_euler_patch_euler_term (n : ℕ) (w : ℂ) : ℂ :=
  ((1 + w) / 2) * w ^ n

/-- Concrete paper-facing package for the Euler-patch chart:
the real axis `|x| < 1/3` stays in the half-plane `Re s > 1`, the Xi-side model at `σ(w)` is the
closed form `(1 + w) / (2(1 - w))` on the subdisk `|w| < 1/3`, and on every closed disk
`|w| ≤ r < 1/3` the Euler terms admit a uniform geometric majorant. -/
def app_horizon_euler_patch_statement : Prop :=
  (∀ x : ℝ, |x| < 1 / 3 → 1 < app_horizon_euler_patch_sigma_real x) ∧
    (∀ w : ℂ, ‖w‖ < 1 / 3 →
      app_horizon_euler_patch_xi_log_derivative (app_horizon_euler_patch_sigma w) =
        (1 + w) / (2 * (1 - w))) ∧
    (∀ r : ℝ, 0 ≤ r → r < 1 / 3 →
      0 < 1 - r ∧
        Summable (fun n : ℕ => ((1 + r) / 2) * r ^ n) ∧
        ∀ w : ℂ, ‖w‖ ≤ r →
          ∀ n : ℕ,
            ‖app_horizon_euler_patch_euler_term n w‖ ≤ ((1 + r) / 2) * r ^ n)

private lemma app_horizon_euler_patch_sigma_real_gt_one (x : ℝ) (hx : |x| < 1 / 3) :
    1 < app_horizon_euler_patch_sigma_real x := by
  have hx_lt : x < 1 / 3 := (abs_lt.mp hx).2
  have hx_gt : -(1 / 3 : ℝ) < x := (abs_lt.mp hx).1
  have hden_pos : 0 < 2 * (1 + x) := by linarith
  have hineq : 2 * (1 + x) < 3 - x := by linarith
  have hdiv := (one_lt_div hden_pos).2 hineq
  simpa [app_horizon_euler_patch_sigma_real] using hdiv

private lemma app_horizon_euler_patch_w_ne_neg_one {w : ℂ} (hw : ‖w‖ < 1 / 3) : w ≠ -1 := by
  intro h
  have : ‖(-1 : ℂ)‖ < 1 / 3 := by simpa [h] using hw
  norm_num at this

private lemma app_horizon_euler_patch_w_ne_two {w : ℂ} (hw : ‖w‖ < 1 / 3) : w ≠ 2 := by
  intro h
  have : ‖(2 : ℂ)‖ < 1 / 3 := by simpa [h] using hw
  norm_num at this

private lemma app_horizon_euler_patch_xi_identity (w : ℂ) (hw : ‖w‖ < 1 / 3) :
    app_horizon_euler_patch_xi_log_derivative (app_horizon_euler_patch_sigma w) =
      (1 + w) / (2 * (1 - w)) := by
  have hw1 : 1 + w ≠ 0 := by
    intro hzero
    apply app_horizon_euler_patch_w_ne_neg_one hw
    have hshift := congrArg (fun z : ℂ => z - 1) hzero
    simpa using hshift
  have hw2 : (2 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (app_horizon_euler_patch_w_ne_two hw).symm
  have hw_ne_one : (1 : ℂ) - w ≠ 0 := by
    intro hzero
    have : ‖(1 : ℂ)‖ < 1 / 3 := by simpa [sub_eq_zero.mp hzero] using hw
    norm_num at this
  unfold app_horizon_euler_patch_xi_log_derivative app_horizon_euler_patch_sigma
  have hrewrite : (2 : ℂ) * (((3 : ℂ) - w) / ((2 : ℂ) * (1 + w))) - 1 =
      (2 * (1 - w)) / (1 + w) := by
    field_simp [hw1]
    ring
  rw [hrewrite]
  field_simp [hw1, hw_ne_one]

private lemma app_horizon_euler_patch_term_bound
    {r : ℝ} (hr0 : 0 ≤ r) {w : ℂ} (hw : ‖w‖ ≤ r) (n : ℕ) :
    ‖app_horizon_euler_patch_euler_term n w‖ ≤ ((1 + r) / 2) * r ^ n := by
  have hnorm_factor :
      ‖(1 + w) / 2‖ ≤ (1 + r) / 2 := by
    calc
      ‖(1 + w) / 2‖ = ‖1 + w‖ / 2 := by simp
      _ ≤ (‖(1 : ℂ)‖ + ‖w‖) / 2 := by
        gcongr
        exact norm_add_le _ _
      _ = (1 + ‖w‖) / 2 := by simp
      _ ≤ (1 + r) / 2 := by gcongr
  have hnorm_ratio :
      ‖w‖ ^ n ≤ r ^ n := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          ‖w‖ ^ (n + 1) = ‖w‖ ^ n * ‖w‖ := by rw [pow_succ]
          _ ≤ r ^ n * r := by
                exact mul_le_mul ih hw (norm_nonneg _) (pow_nonneg hr0 _)
          _ = r ^ (n + 1) := by rw [pow_succ]
  calc
    ‖app_horizon_euler_patch_euler_term n w‖
        = ‖(1 + w) / 2‖ * ‖w‖ ^ n := by
            simp [app_horizon_euler_patch_euler_term, norm_pow]
    _ ≤ ((1 + r) / 2) * r ^ n := by
          exact mul_le_mul hnorm_factor hnorm_ratio (pow_nonneg (norm_nonneg _) _) (by positivity)

/-- Paper label: `thm:app-horizon-euler-patch`. The Möbius chart
`σ(w) = (3 - w)/(2(1 + w))` sends the real interval `|x| < 1/3` into `Re s > 1`, the Xi-side
closed form at `σ(w)` is `(1 + w)/(2(1 - w))` throughout the subdisk `|w| < 1/3`, and every closed
disk `|w| ≤ r < 1/3` admits the uniform geometric majorant
`((1 + r)/2) * r^n` for the Euler terms, hence uniform absolute convergence there. -/
theorem paper_app_horizon_euler_patch : app_horizon_euler_patch_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact app_horizon_euler_patch_sigma_real_gt_one x hx
  · intro w hw
    exact app_horizon_euler_patch_xi_identity w hw
  · intro r hr0 hrlt
    have hr1 : r < 1 := by linarith
    refine ⟨by linarith, (summable_geometric_of_lt_one hr0 hr1).mul_left _, ?_⟩
    intro w hw n
    exact app_horizon_euler_patch_term_bound hr0 hw n

end

end Omega.UnitCirclePhaseArithmetic
