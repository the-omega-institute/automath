import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- A concrete log-max defect seed: the positive part of the excess radius above the ellipse
parameter. -/
def xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_log_max_term
    (L r : ℝ) : ℝ :=
  max 0 (r - L)

/-- The finite Mahler-Green defect modelled as a sum of nonnegative log-max terms. -/
def xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_defect
    {n : ℕ} (L : ℝ) (radii : Fin n → ℝ) : ℝ :=
  ∑ i, xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_log_max_term L (radii i)

/-- The limiting Joukowsky interval obtained as the ellipse parameter tends to one. -/
def xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_interval
    (x : ℝ) : Prop :=
  -2 ≤ x ∧ x ≤ 2

/-- A one-parameter closed ellipse window whose endpoint at `L = 1` is `[-2, 2]`. -/
def xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_ellipse
    (L x : ℝ) : Prop :=
  -(L + 1) ≤ x ∧ x ≤ L + 1

/-- Paper label: `thm:xi-joukowsky-ellipse-defect-nonnegativity-interval-limit`. The concrete
finite defect is a sum of nonnegative log-max terms; a vanished term is exactly the no-excess
radius condition, and the limiting interval embeds into every closed ellipse window with
parameter `L ≥ 1`. -/
theorem paper_xi_joukowsky_ellipse_defect_nonnegativity_interval_limit
    {n : ℕ} (L : ℝ) (hL : 1 ≤ L) (radii : Fin n → ℝ) :
    0 ≤ xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_defect L radii ∧
      (∀ i : Fin n,
        xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_log_max_term L (radii i) = 0 ↔
          radii i ≤ L) ∧
      (∀ x : ℝ,
        xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_interval x →
          xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_ellipse L x) := by
  constructor
  · dsimp [xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_defect,
      xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_log_max_term]
    exact Finset.sum_nonneg fun i _ => le_max_left 0 (radii i - L)
  constructor
  · intro i
    dsimp [xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_log_max_term]
    constructor
    · intro h
      have hle : radii i - L ≤ 0 := (max_eq_left_iff.mp h)
      linarith
    · intro h
      exact max_eq_left (by linarith)
  · intro x hx
    rcases hx with ⟨hxlow, hxhigh⟩
    dsimp [xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_interval,
      xi_joukowsky_ellipse_defect_nonnegativity_interval_limit_ellipse] at *
    constructor <;> linarith

end

end Omega.Zeta
