import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

namespace Omega.Zeta

/-- Concrete audit data for the Toeplitz--Caratheodory completion tail-exclusion statement. -/
structure xi_toeplitz_caratheodory_completion_tail_exclusion_Data where
  xi_toeplitz_caratheodory_completion_tail_exclusion_N : ℕ
  xi_toeplitz_caratheodory_completion_tail_exclusion_a0 : ℝ
  xi_toeplitz_caratheodory_completion_tail_exclusion_r : ℝ
  xi_toeplitz_caratheodory_completion_tail_exclusion_epsilon : ℝ
  xi_toeplitz_caratheodory_completion_tail_exclusion_f : ℂ → ℂ
  xi_toeplitz_caratheodory_completion_tail_exclusion_g : ℂ → ℂ
  xi_toeplitz_caratheodory_completion_tail_exclusion_toeplitz_psd :
    0 ≤ xi_toeplitz_caratheodory_completion_tail_exclusion_a0
  xi_toeplitz_caratheodory_completion_tail_exclusion_radius_pos :
    0 < xi_toeplitz_caratheodory_completion_tail_exclusion_r
  xi_toeplitz_caratheodory_completion_tail_exclusion_radius_lt_one :
    xi_toeplitz_caratheodory_completion_tail_exclusion_r < 1
  xi_toeplitz_caratheodory_completion_tail_exclusion_completion_lower :
    ∀ z : ℂ, ‖z‖ ≤ xi_toeplitz_caratheodory_completion_tail_exclusion_r →
      (1 - xi_toeplitz_caratheodory_completion_tail_exclusion_r) /
          (1 + xi_toeplitz_caratheodory_completion_tail_exclusion_r) *
          xi_toeplitz_caratheodory_completion_tail_exclusion_a0 ≤
        (xi_toeplitz_caratheodory_completion_tail_exclusion_g z).re
  xi_toeplitz_caratheodory_completion_tail_exclusion_tail_error :
    ∀ z : ℂ, ‖z‖ ≤ xi_toeplitz_caratheodory_completion_tail_exclusion_r →
      ‖xi_toeplitz_caratheodory_completion_tail_exclusion_f z -
          xi_toeplitz_caratheodory_completion_tail_exclusion_g z‖ ≤
        2 * xi_toeplitz_caratheodory_completion_tail_exclusion_epsilon
  xi_toeplitz_caratheodory_completion_tail_exclusion_positive_margin :
    2 * xi_toeplitz_caratheodory_completion_tail_exclusion_epsilon <
      (1 - xi_toeplitz_caratheodory_completion_tail_exclusion_r) /
          (1 + xi_toeplitz_caratheodory_completion_tail_exclusion_r) *
          xi_toeplitz_caratheodory_completion_tail_exclusion_a0

namespace xi_toeplitz_caratheodory_completion_tail_exclusion_Data

/-- The lower Poisson-kernel scale appearing in the completion bound. -/
noncomputable def xi_toeplitz_caratheodory_completion_tail_exclusion_lowerScale
    (D : xi_toeplitz_caratheodory_completion_tail_exclusion_Data) : ℝ :=
  (1 - D.xi_toeplitz_caratheodory_completion_tail_exclusion_r) /
      (1 + D.xi_toeplitz_caratheodory_completion_tail_exclusion_r) *
    D.xi_toeplitz_caratheodory_completion_tail_exclusion_a0

/-- Concrete Toeplitz PSD wrapper: the zeroth moment is nonnegative. -/
def xi_toeplitz_caratheodory_completion_tail_exclusion_ToeplitzPSD
    (D : xi_toeplitz_caratheodory_completion_tail_exclusion_Data) : Prop :=
  0 ≤ D.xi_toeplitz_caratheodory_completion_tail_exclusion_a0

/-- Concrete Caratheodory completion lower real-part wrapper. -/
def xi_toeplitz_caratheodory_completion_tail_exclusion_CaratheodoryCompletionLower
    (D : xi_toeplitz_caratheodory_completion_tail_exclusion_Data) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ D.xi_toeplitz_caratheodory_completion_tail_exclusion_r →
    D.xi_toeplitz_caratheodory_completion_tail_exclusion_lowerScale ≤
      (D.xi_toeplitz_caratheodory_completion_tail_exclusion_g z).re

/-- Concrete tail-error wrapper on the closed radius-`r` disk. -/
def xi_toeplitz_caratheodory_completion_tail_exclusion_TailError
    (D : xi_toeplitz_caratheodory_completion_tail_exclusion_Data) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ D.xi_toeplitz_caratheodory_completion_tail_exclusion_r →
    ‖D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z -
        D.xi_toeplitz_caratheodory_completion_tail_exclusion_g z‖ ≤
      2 * D.xi_toeplitz_caratheodory_completion_tail_exclusion_epsilon

/-- Quantitative lower bound for the real part of the original analytic function. -/
def xi_toeplitz_caratheodory_completion_tail_exclusion_PositiveTailBound
    (D : xi_toeplitz_caratheodory_completion_tail_exclusion_Data) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ D.xi_toeplitz_caratheodory_completion_tail_exclusion_r →
    D.xi_toeplitz_caratheodory_completion_tail_exclusion_lowerScale -
        2 * D.xi_toeplitz_caratheodory_completion_tail_exclusion_epsilon ≤
      (D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z).re

/-- Zero exclusion on the closed radius-`r` disk. -/
def xi_toeplitz_caratheodory_completion_tail_exclusion_NoZeros
    (D : xi_toeplitz_caratheodory_completion_tail_exclusion_Data) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ D.xi_toeplitz_caratheodory_completion_tail_exclusion_r →
    D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z ≠ 0

end xi_toeplitz_caratheodory_completion_tail_exclusion_Data

open xi_toeplitz_caratheodory_completion_tail_exclusion_Data

/-- Paper label: `thm:xi-toeplitz-caratheodory-completion-tail-exclusion`. -/
theorem paper_xi_toeplitz_caratheodory_completion_tail_exclusion
    (D : xi_toeplitz_caratheodory_completion_tail_exclusion_Data) :
    xi_toeplitz_caratheodory_completion_tail_exclusion_PositiveTailBound D ∧
      xi_toeplitz_caratheodory_completion_tail_exclusion_NoZeros D := by
  have hbound :
      xi_toeplitz_caratheodory_completion_tail_exclusion_PositiveTailBound D := by
    intro z hz
    have hcompletion :
        D.xi_toeplitz_caratheodory_completion_tail_exclusion_lowerScale ≤
          (D.xi_toeplitz_caratheodory_completion_tail_exclusion_g z).re := by
      simpa [xi_toeplitz_caratheodory_completion_tail_exclusion_lowerScale] using
        D.xi_toeplitz_caratheodory_completion_tail_exclusion_completion_lower z hz
    have htail :
        ‖D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z -
            D.xi_toeplitz_caratheodory_completion_tail_exclusion_g z‖ ≤
          2 * D.xi_toeplitz_caratheodory_completion_tail_exclusion_epsilon :=
      D.xi_toeplitz_caratheodory_completion_tail_exclusion_tail_error z hz
    have hreal :
        -‖D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z -
            D.xi_toeplitz_caratheodory_completion_tail_exclusion_g z‖ ≤
          (D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z -
            D.xi_toeplitz_caratheodory_completion_tail_exclusion_g z).re := by
      have habs :
          |(D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z -
              D.xi_toeplitz_caratheodory_completion_tail_exclusion_g z).re| ≤
            ‖D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z -
              D.xi_toeplitz_caratheodory_completion_tail_exclusion_g z‖ :=
        Complex.abs_re_le_norm
          (D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z -
            D.xi_toeplitz_caratheodory_completion_tail_exclusion_g z)
      exact (abs_le.mp habs).1
    have hfg :
        (D.xi_toeplitz_caratheodory_completion_tail_exclusion_g z).re -
            ‖D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z -
              D.xi_toeplitz_caratheodory_completion_tail_exclusion_g z‖ ≤
          (D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z).re := by
      rw [Complex.sub_re] at hreal
      linarith
    linarith
  constructor
  · exact hbound
  · intro z hz hz0
    have hpositive := hbound z hz
    have hmargin :
        0 <
          D.xi_toeplitz_caratheodory_completion_tail_exclusion_lowerScale -
            2 * D.xi_toeplitz_caratheodory_completion_tail_exclusion_epsilon := by
      simpa [xi_toeplitz_caratheodory_completion_tail_exclusion_lowerScale, sub_pos] using
        D.xi_toeplitz_caratheodory_completion_tail_exclusion_positive_margin
    have hfpos : 0 < (D.xi_toeplitz_caratheodory_completion_tail_exclusion_f z).re :=
      lt_of_lt_of_le hmargin hpositive
    simp [hz0] at hfpos

end Omega.Zeta
