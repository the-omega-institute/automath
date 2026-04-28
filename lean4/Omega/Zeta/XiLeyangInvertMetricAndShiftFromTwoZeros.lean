import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete two-zero finite-size scaling data. The two observed zeros share the same shift and
metric factor but have distinct node constants, so subtracting the expansions isolates the metric
and substituting back isolates the shift. -/
structure xi_leyang_invert_metric_and_shift_from_two_zeros_Data where
  xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA : ℝ
  xi_leyang_invert_metric_and_shift_from_two_zeros_nodeB : ℝ
  xi_leyang_invert_metric_and_shift_from_two_zeros_metric : ℝ
  xi_leyang_invert_metric_and_shift_from_two_zeros_shift : ℝ
  xi_leyang_invert_metric_and_shift_from_two_zeros_zeroA : ℕ → ℝ
  xi_leyang_invert_metric_and_shift_from_two_zeros_zeroB : ℕ → ℝ
  xi_leyang_invert_metric_and_shift_from_two_zeros_residualA : ℕ → ℝ
  xi_leyang_invert_metric_and_shift_from_two_zeros_residualB : ℕ → ℝ
  xi_leyang_invert_metric_and_shift_from_two_zeros_errorBudget : ℕ → ℝ
  xi_leyang_invert_metric_and_shift_from_two_zeros_nodes_separated :
    xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA ≠
      xi_leyang_invert_metric_and_shift_from_two_zeros_nodeB
  xi_leyang_invert_metric_and_shift_from_two_zeros_error_nonneg :
    ∀ n, 0 ≤ xi_leyang_invert_metric_and_shift_from_two_zeros_errorBudget n
  xi_leyang_invert_metric_and_shift_from_two_zeros_zeroA_expansion :
    ∀ n,
      xi_leyang_invert_metric_and_shift_from_two_zeros_zeroA n =
        xi_leyang_invert_metric_and_shift_from_two_zeros_shift +
          xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA *
            xi_leyang_invert_metric_and_shift_from_two_zeros_metric +
          xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n
  xi_leyang_invert_metric_and_shift_from_two_zeros_zeroB_expansion :
    ∀ n,
      xi_leyang_invert_metric_and_shift_from_two_zeros_zeroB n =
        xi_leyang_invert_metric_and_shift_from_two_zeros_shift +
          xi_leyang_invert_metric_and_shift_from_two_zeros_nodeB *
            xi_leyang_invert_metric_and_shift_from_two_zeros_metric +
          xi_leyang_invert_metric_and_shift_from_two_zeros_residualB n
  xi_leyang_invert_metric_and_shift_from_two_zeros_residualA_bound :
    ∀ n,
      ‖xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n‖ ≤
        xi_leyang_invert_metric_and_shift_from_two_zeros_errorBudget n
  xi_leyang_invert_metric_and_shift_from_two_zeros_residualB_bound :
    ∀ n,
      ‖xi_leyang_invert_metric_and_shift_from_two_zeros_residualB n‖ ≤
        xi_leyang_invert_metric_and_shift_from_two_zeros_errorBudget n

/-- Metric estimate obtained by subtracting the two zero expansions. -/
def xi_leyang_invert_metric_and_shift_from_two_zeros_metricEstimate
    (D : xi_leyang_invert_metric_and_shift_from_two_zeros_Data) (n : ℕ) : ℝ :=
  (D.xi_leyang_invert_metric_and_shift_from_two_zeros_zeroA n -
      D.xi_leyang_invert_metric_and_shift_from_two_zeros_zeroB n) /
    (D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA -
      D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeB)

/-- Shift estimate obtained by substituting the recovered metric estimate into the first zero. -/
def xi_leyang_invert_metric_and_shift_from_two_zeros_shiftEstimate
    (D : xi_leyang_invert_metric_and_shift_from_two_zeros_Data) (n : ℕ) : ℝ :=
  D.xi_leyang_invert_metric_and_shift_from_two_zeros_zeroA n -
    D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA *
      xi_leyang_invert_metric_and_shift_from_two_zeros_metricEstimate D n

/-- The concrete finite-size stability statement for the two-zero inversion. -/
def xi_leyang_invert_metric_and_shift_from_two_zeros_statement
    (D : xi_leyang_invert_metric_and_shift_from_two_zeros_Data) : Prop :=
  ∀ n,
    ‖xi_leyang_invert_metric_and_shift_from_two_zeros_metricEstimate D n -
        D.xi_leyang_invert_metric_and_shift_from_two_zeros_metric‖ ≤
      (2 / ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA -
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeB‖) *
        D.xi_leyang_invert_metric_and_shift_from_two_zeros_errorBudget n ∧
      ‖xi_leyang_invert_metric_and_shift_from_two_zeros_shiftEstimate D n -
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_shift‖ ≤
        (1 +
            ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA‖ *
              (2 / ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA -
                D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeB‖)) *
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_errorBudget n

lemma xi_leyang_invert_metric_and_shift_from_two_zeros_metric_error_identity
    (D : xi_leyang_invert_metric_and_shift_from_two_zeros_Data) (n : ℕ) :
    xi_leyang_invert_metric_and_shift_from_two_zeros_metricEstimate D n -
        D.xi_leyang_invert_metric_and_shift_from_two_zeros_metric =
      (D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n -
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualB n) /
        (D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA -
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeB) := by
  have hden :
      D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA -
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeB ≠ 0 := by
    exact sub_ne_zero.mpr D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodes_separated
  rw [xi_leyang_invert_metric_and_shift_from_two_zeros_metricEstimate,
    D.xi_leyang_invert_metric_and_shift_from_two_zeros_zeroA_expansion n,
    D.xi_leyang_invert_metric_and_shift_from_two_zeros_zeroB_expansion n]
  field_simp [hden]
  ring

lemma xi_leyang_invert_metric_and_shift_from_two_zeros_shift_error_identity
    (D : xi_leyang_invert_metric_and_shift_from_two_zeros_Data) (n : ℕ) :
    xi_leyang_invert_metric_and_shift_from_two_zeros_shiftEstimate D n -
        D.xi_leyang_invert_metric_and_shift_from_two_zeros_shift =
      D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n -
        D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA *
          (xi_leyang_invert_metric_and_shift_from_two_zeros_metricEstimate D n -
            D.xi_leyang_invert_metric_and_shift_from_two_zeros_metric) := by
  rw [xi_leyang_invert_metric_and_shift_from_two_zeros_shiftEstimate,
    D.xi_leyang_invert_metric_and_shift_from_two_zeros_zeroA_expansion n]
  ring

/-- Paper label: `thm:xi-leyang-invert-metric-and-shift-from-two-zeros`. -/
theorem paper_xi_leyang_invert_metric_and_shift_from_two_zeros
    (D : xi_leyang_invert_metric_and_shift_from_two_zeros_Data) :
    xi_leyang_invert_metric_and_shift_from_two_zeros_statement D := by
  intro n
  let d :=
    D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA -
      D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeB
  let e := D.xi_leyang_invert_metric_and_shift_from_two_zeros_errorBudget n
  have hd_ne : d ≠ 0 := by
    exact sub_ne_zero.mpr D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodes_separated
  have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
  have he : 0 ≤ e :=
    D.xi_leyang_invert_metric_and_shift_from_two_zeros_error_nonneg n
  have hres_sum :
      ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n -
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualB n‖ ≤
        2 * e := by
    calc
      ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n -
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualB n‖
          ≤ ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n‖ +
              ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualB n‖ := by
            simpa [sub_eq_add_neg] using
              norm_add_le
                (D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n)
                (-(D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualB n))
      _ ≤ e + e := by
            gcongr
            · exact D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA_bound n
            · simpa using
                D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualB_bound n
      _ = 2 * e := by ring
  have hmetric :
      ‖xi_leyang_invert_metric_and_shift_from_two_zeros_metricEstimate D n -
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_metric‖ ≤
        (2 / ‖d‖) * e := by
    rw [xi_leyang_invert_metric_and_shift_from_two_zeros_metric_error_identity D n]
    calc
      ‖(D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n -
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualB n) / d‖
          = ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n -
              D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualB n‖ / ‖d‖ := by
            simp [norm_div]
      _ ≤ (2 * e) / ‖d‖ := by
            exact div_le_div_of_nonneg_right hres_sum (le_of_lt hd_pos)
      _ = (2 / ‖d‖) * e := by ring
  have hshift :
      ‖xi_leyang_invert_metric_and_shift_from_two_zeros_shiftEstimate D n -
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_shift‖ ≤
        (1 +
            ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA‖ *
              (2 / ‖d‖)) * e := by
    rw [xi_leyang_invert_metric_and_shift_from_two_zeros_shift_error_identity D n]
    calc
      ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n -
          D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA *
            (xi_leyang_invert_metric_and_shift_from_two_zeros_metricEstimate D n -
              D.xi_leyang_invert_metric_and_shift_from_two_zeros_metric)‖
          ≤ ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n‖ +
              ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA *
                (xi_leyang_invert_metric_and_shift_from_two_zeros_metricEstimate D n -
                  D.xi_leyang_invert_metric_and_shift_from_two_zeros_metric)‖ := by
            simpa [sub_eq_add_neg] using
              norm_add_le
                (D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n)
                (-(D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA *
                  (xi_leyang_invert_metric_and_shift_from_two_zeros_metricEstimate D n -
                    D.xi_leyang_invert_metric_and_shift_from_two_zeros_metric)))
      _ = ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA n‖ +
              ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA‖ *
                ‖xi_leyang_invert_metric_and_shift_from_two_zeros_metricEstimate D n -
                  D.xi_leyang_invert_metric_and_shift_from_two_zeros_metric‖ := by
            rw [norm_mul]
      _ ≤ e +
              ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA‖ *
                ((2 / ‖d‖) * e) := by
            gcongr
            exact D.xi_leyang_invert_metric_and_shift_from_two_zeros_residualA_bound n
      _ = (1 +
            ‖D.xi_leyang_invert_metric_and_shift_from_two_zeros_nodeA‖ *
              (2 / ‖d‖)) * e := by ring
  simpa [xi_leyang_invert_metric_and_shift_from_two_zeros_statement, d] using
    And.intro hmetric hshift

end

end Omega.Zeta
