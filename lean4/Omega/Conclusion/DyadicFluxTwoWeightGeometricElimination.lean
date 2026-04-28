import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete two-weight dyadic flux package. The weighted Stokes estimate is recorded as an exact
log-scale dimension-shift identity for each vanishing order. -/
structure conclusion_dyadic_flux_two_weight_geometric_elimination_data where
  conclusion_dyadic_flux_two_weight_geometric_elimination_low_order : ℕ
  conclusion_dyadic_flux_two_weight_geometric_elimination_high_order : ℕ
  conclusion_dyadic_flux_two_weight_geometric_elimination_log_flux : ℕ → ℕ → ℚ
  conclusion_dyadic_flux_two_weight_geometric_elimination_intercept : ℕ → ℚ
  conclusion_dyadic_flux_two_weight_geometric_elimination_weighted_stokes_estimate :
    ∀ q n,
      conclusion_dyadic_flux_two_weight_geometric_elimination_log_flux q n =
        conclusion_dyadic_flux_two_weight_geometric_elimination_intercept q - (q : ℚ) * n
  conclusion_dyadic_flux_two_weight_geometric_elimination_intercepts_match :
    conclusion_dyadic_flux_two_weight_geometric_elimination_intercept
        conclusion_dyadic_flux_two_weight_geometric_elimination_high_order =
      conclusion_dyadic_flux_two_weight_geometric_elimination_intercept
        conclusion_dyadic_flux_two_weight_geometric_elimination_low_order

/-- The normalized dyadic log-slope obtained by dividing the two weighted flux laws. -/
def conclusion_dyadic_flux_two_weight_geometric_elimination_logarithmic_slope
    (D : conclusion_dyadic_flux_two_weight_geometric_elimination_data) (n : ℕ) : ℚ :=
  (D.conclusion_dyadic_flux_two_weight_geometric_elimination_log_flux
      D.conclusion_dyadic_flux_two_weight_geometric_elimination_low_order n -
    D.conclusion_dyadic_flux_two_weight_geometric_elimination_log_flux
      D.conclusion_dyadic_flux_two_weight_geometric_elimination_high_order n) / n

/-- The exact geometric-elimination statement, stronger than the corresponding slope limit:
every positive dyadic scale has the limiting slope read off from the two vanishing orders. -/
def conclusion_dyadic_flux_two_weight_geometric_elimination_statement
    (D : conclusion_dyadic_flux_two_weight_geometric_elimination_data) : Prop :=
  ∀ n : ℕ, 0 < n →
    conclusion_dyadic_flux_two_weight_geometric_elimination_logarithmic_slope D n =
      D.conclusion_dyadic_flux_two_weight_geometric_elimination_high_order -
        D.conclusion_dyadic_flux_two_weight_geometric_elimination_low_order

/-- Paper label:
`thm:conclusion-dyadic-flux-two-weight-geometric-elimination`. -/
theorem paper_conclusion_dyadic_flux_two_weight_geometric_elimination
    (D : conclusion_dyadic_flux_two_weight_geometric_elimination_data) :
    conclusion_dyadic_flux_two_weight_geometric_elimination_statement D := by
  intro n hn
  have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  unfold conclusion_dyadic_flux_two_weight_geometric_elimination_logarithmic_slope
  rw [D.conclusion_dyadic_flux_two_weight_geometric_elimination_weighted_stokes_estimate,
    D.conclusion_dyadic_flux_two_weight_geometric_elimination_weighted_stokes_estimate,
    D.conclusion_dyadic_flux_two_weight_geometric_elimination_intercepts_match]
  field_simp [hn_ne]
  ring

end Omega.Conclusion
