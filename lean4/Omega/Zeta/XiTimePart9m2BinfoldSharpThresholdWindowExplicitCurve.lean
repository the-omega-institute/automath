import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete datum for the continuous critical bin-fold success curve.  The constants and the
dyadic exponential are recorded explicitly; the limiting curve and window width are derived
definitions below. -/
structure xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_data where
  xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_phi : ℝ
  xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_phi_inv : ℝ
  xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_sqrt5 : ℝ
  xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_two_pow : ℝ → ℝ
  xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_log2_phi : ℝ

namespace xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_data

/-- The explicit three-piece critical success curve in the `b` coordinate. -/
noncomputable def xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_limit_at
    (D : xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_data) (b : ℝ) : ℝ :=
  if b ≤ -D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_log2_phi then
    D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_phi ^ 2 *
      D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_two_pow b /
        D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_sqrt5
  else if b ≤ 0 then
    (D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_phi *
          D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_two_pow b +
        D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_phi_inv) /
      D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_sqrt5
  else
    1

/-- The active transition interval is `[-log₂ φ, 0]`, so its width is `log₂ φ`. -/
def xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_transition_width
    (D : xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_data) : ℝ :=
  D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_log2_phi

end xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_data

/-- Paper label: `thm:xi-time-part9m2-binfold-sharp-threshold-window-explicit-curve`. -/
theorem paper_xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve
    (D : xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_data) :
    (∀ b,
      D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_limit_at b =
        if b ≤ -D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_log2_phi then
          D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_phi ^ 2 *
            D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_two_pow b /
              D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_sqrt5
        else if b ≤ 0 then
          (D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_phi *
                D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_two_pow b +
              D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_phi_inv) /
            D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_sqrt5
        else
          1) ∧
      D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_transition_width =
        D.xi_time_part9m2_binfold_sharp_threshold_window_explicit_curve_log2_phi := by
  constructor
  · intro b
    rfl
  · rfl

end Omega.Zeta
