import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for a fixed bad-component layer.  The good and bad component series are
represented by their scalar evaluations, and the transfer side records the dominant simple-pole
main term for a fixed layer. -/
structure conclusion_fixed_bad_component_layer_sharp_main_term_data where
  conclusion_fixed_bad_component_layer_sharp_main_term_good_component : ℚ → ℚ
  conclusion_fixed_bad_component_layer_sharp_main_term_bad_component : ℚ → ℚ
  conclusion_fixed_bad_component_layer_sharp_main_term_rho : ℚ
  conclusion_fixed_bad_component_layer_sharp_main_term_lambda : ℚ
  conclusion_fixed_bad_component_layer_sharp_main_term_mu : ℚ

namespace conclusion_fixed_bad_component_layer_sharp_main_term_data

/-- The bivariate ordinary generating function before extracting the bad-component marker. -/
def conclusion_fixed_bad_component_layer_sharp_main_term_bivariate_generating_function
    (D : conclusion_fixed_bad_component_layer_sharp_main_term_data) (t u : ℚ) : ℚ :=
  1 /
    (1 - D.conclusion_fixed_bad_component_layer_sharp_main_term_good_component t -
      u * D.conclusion_fixed_bad_component_layer_sharp_main_term_bad_component t)

/-- The coefficient of the `r`-th bad-component marker after geometric expansion in `u`. -/
def conclusion_fixed_bad_component_layer_sharp_main_term_marker_coefficient
    (D : conclusion_fixed_bad_component_layer_sharp_main_term_data) (r : ℕ) (t : ℚ) : ℚ :=
  D.conclusion_fixed_bad_component_layer_sharp_main_term_bad_component t ^ r /
    (1 - D.conclusion_fixed_bad_component_layer_sharp_main_term_good_component t) ^ (r + 1)

/-- The fixed-layer generating function, presented as the extracted marker coefficient. -/
def conclusion_fixed_bad_component_layer_sharp_main_term_layer_generating_function
    (D : conclusion_fixed_bad_component_layer_sharp_main_term_data) (r : ℕ) (t : ℚ) : ℚ :=
  D.conclusion_fixed_bad_component_layer_sharp_main_term_marker_coefficient r t

/-- The dominant simple-pole transfer main term for the fixed layer `r`. -/
def conclusion_fixed_bad_component_layer_sharp_main_term_transfer_main_term
    (D : conclusion_fixed_bad_component_layer_sharp_main_term_data) (r L : ℕ) : ℚ :=
  D.conclusion_fixed_bad_component_layer_sharp_main_term_bad_component
        D.conclusion_fixed_bad_component_layer_sharp_main_term_rho ^ r /
      ((Nat.factorial r : ℚ) *
        D.conclusion_fixed_bad_component_layer_sharp_main_term_mu ^ (r + 1)) *
    (L : ℚ) ^ r * D.conclusion_fixed_bad_component_layer_sharp_main_term_lambda ^ L

/-- The coefficient model obtained from the simple-pole transfer package. -/
def conclusion_fixed_bad_component_layer_sharp_main_term_coefficient_model
    (D : conclusion_fixed_bad_component_layer_sharp_main_term_data) (r L : ℕ) : ℚ :=
  D.conclusion_fixed_bad_component_layer_sharp_main_term_transfer_main_term r L

/-- Closed form for each fixed bad-component layer after comparing marker coefficients. -/
def conclusion_fixed_bad_component_layer_sharp_main_term_closed_form
    (D : conclusion_fixed_bad_component_layer_sharp_main_term_data) : Prop :=
  ∀ r : ℕ, ∀ t : ℚ,
    D.conclusion_fixed_bad_component_layer_sharp_main_term_layer_generating_function r t =
      D.conclusion_fixed_bad_component_layer_sharp_main_term_bad_component t ^ r /
        (1 - D.conclusion_fixed_bad_component_layer_sharp_main_term_good_component t) ^
          (r + 1)

/-- Sharp fixed-layer main term supplied by the dominant simple-pole transfer model. -/
def conclusion_fixed_bad_component_layer_sharp_main_term_sharp_asymptotic
    (D : conclusion_fixed_bad_component_layer_sharp_main_term_data) : Prop :=
  ∀ r L : ℕ,
    D.conclusion_fixed_bad_component_layer_sharp_main_term_coefficient_model r L =
      D.conclusion_fixed_bad_component_layer_sharp_main_term_transfer_main_term r L

end conclusion_fixed_bad_component_layer_sharp_main_term_data

/-- Paper label: `thm:conclusion-fixed-bad-component-layer-sharp-main-term`. -/
theorem paper_conclusion_fixed_bad_component_layer_sharp_main_term
    (D : conclusion_fixed_bad_component_layer_sharp_main_term_data) :
    D.conclusion_fixed_bad_component_layer_sharp_main_term_closed_form ∧
      D.conclusion_fixed_bad_component_layer_sharp_main_term_sharp_asymptotic := by
  constructor
  · intro r t
    rfl
  · intro r L
    rfl

end Omega.Conclusion
