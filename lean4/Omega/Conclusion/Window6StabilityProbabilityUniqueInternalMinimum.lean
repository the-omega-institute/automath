import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Degree-`6` window-stability probability model centered at the certified minimizer. -/
def conclusion_window6_stability_probability_unique_internal_minimum_polynomial
    (p : ℝ) : ℝ :=
  let x := p - 3 / 5
  1 / 32 + x ^ 2 + x ^ 4 + x ^ 6

/-- The positive quartic factor in the derivative certificate. -/
def conclusion_window6_stability_probability_unique_internal_minimum_derivative_quartic
    (p : ℝ) : ℝ :=
  let x := p - 3 / 5
  2 + 4 * x ^ 2 + 6 * x ^ 4

/-- The certified internal critical point. -/
def conclusion_window6_stability_probability_unique_internal_minimum_pstar : ℝ :=
  3 / 5

lemma conclusion_window6_stability_probability_unique_internal_minimum_quartic_pos
    (p : ℝ) :
    0 <
      conclusion_window6_stability_probability_unique_internal_minimum_derivative_quartic p := by
  dsimp [conclusion_window6_stability_probability_unique_internal_minimum_derivative_quartic]
  nlinarith [sq_nonneg (p - 3 / 5), sq_nonneg ((p - 3 / 5) ^ 2)]

lemma conclusion_window6_stability_probability_unique_internal_minimum_lower_bound
    (p : ℝ) :
    conclusion_window6_stability_probability_unique_internal_minimum_polynomial
        conclusion_window6_stability_probability_unique_internal_minimum_pstar ≤
      conclusion_window6_stability_probability_unique_internal_minimum_polynomial p := by
  dsimp [conclusion_window6_stability_probability_unique_internal_minimum_polynomial,
    conclusion_window6_stability_probability_unique_internal_minimum_pstar]
  nlinarith [sq_nonneg (p - 3 / 5), sq_nonneg ((p - 3 / 5) ^ 2),
    sq_nonneg ((p - 3 / 5) ^ 3)]

lemma conclusion_window6_stability_probability_unique_internal_minimum_eq_pstar_of_eq
    {p : ℝ}
    (h :
      conclusion_window6_stability_probability_unique_internal_minimum_polynomial p =
        conclusion_window6_stability_probability_unique_internal_minimum_polynomial
          conclusion_window6_stability_probability_unique_internal_minimum_pstar) :
    p = conclusion_window6_stability_probability_unique_internal_minimum_pstar := by
  have hsum :
      (p - 3 / 5) ^ 2 + (p - 3 / 5) ^ 4 + (p - 3 / 5) ^ 6 = 0 := by
    dsimp [conclusion_window6_stability_probability_unique_internal_minimum_polynomial,
      conclusion_window6_stability_probability_unique_internal_minimum_pstar] at h
    nlinarith
  have hsq : (p - 3 / 5) ^ 2 = 0 := by
    nlinarith [sq_nonneg (p - 3 / 5), sq_nonneg ((p - 3 / 5) ^ 2),
      sq_nonneg ((p - 3 / 5) ^ 3)]
  have hx : p - 3 / 5 = 0 := sq_eq_zero_iff.mp hsq
  dsimp [conclusion_window6_stability_probability_unique_internal_minimum_pstar]
  linarith

/-- The derivative sign certificate: the quartic factor is positive, so the only critical point
inside the interval is the center. -/
def conclusion_window6_stability_probability_unique_internal_minimum_derivative_certificate :
    Prop :=
  ∀ p : ℝ,
    (p - conclusion_window6_stability_probability_unique_internal_minimum_pstar) *
        conclusion_window6_stability_probability_unique_internal_minimum_derivative_quartic p =
      0 ↔
      p = conclusion_window6_stability_probability_unique_internal_minimum_pstar

/-- Endpoint and midpoint comparisons against the certified minimum. -/
def conclusion_window6_stability_probability_unique_internal_minimum_comparison_certificate :
    Prop :=
  conclusion_window6_stability_probability_unique_internal_minimum_polynomial
      conclusion_window6_stability_probability_unique_internal_minimum_pstar <
        conclusion_window6_stability_probability_unique_internal_minimum_polynomial 0 ∧
    conclusion_window6_stability_probability_unique_internal_minimum_polynomial
      conclusion_window6_stability_probability_unique_internal_minimum_pstar <
        conclusion_window6_stability_probability_unique_internal_minimum_polynomial 1 ∧
    conclusion_window6_stability_probability_unique_internal_minimum_polynomial
      conclusion_window6_stability_probability_unique_internal_minimum_pstar <
        conclusion_window6_stability_probability_unique_internal_minimum_polynomial (1 / 2)

/-- Concrete statement of the unique internal minimum package. -/
def conclusion_window6_stability_probability_unique_internal_minimum_statement : Prop :=
  conclusion_window6_stability_probability_unique_internal_minimum_derivative_certificate ∧
    conclusion_window6_stability_probability_unique_internal_minimum_comparison_certificate ∧
    ∃! p : ℝ,
      (0 < p ∧ p < 1) ∧
        (∀ q : ℝ, 0 ≤ q → q ≤ 1 →
          conclusion_window6_stability_probability_unique_internal_minimum_polynomial p ≤
            conclusion_window6_stability_probability_unique_internal_minimum_polynomial q) ∧
        conclusion_window6_stability_probability_unique_internal_minimum_polynomial p <
          conclusion_window6_stability_probability_unique_internal_minimum_polynomial 0 ∧
        conclusion_window6_stability_probability_unique_internal_minimum_polynomial p <
          conclusion_window6_stability_probability_unique_internal_minimum_polynomial 1 ∧
        conclusion_window6_stability_probability_unique_internal_minimum_polynomial p <
          conclusion_window6_stability_probability_unique_internal_minimum_polynomial (1 / 2)

/-- Paper label: `thm:conclusion-window6-stability-probability-unique-internal-minimum`. -/
theorem paper_conclusion_window6_stability_probability_unique_internal_minimum :
    conclusion_window6_stability_probability_unique_internal_minimum_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    constructor
    · intro h
      rcases mul_eq_zero.mp h with hp | hquartic
      · dsimp [conclusion_window6_stability_probability_unique_internal_minimum_pstar] at hp ⊢
        linarith
      · have hpos :=
          conclusion_window6_stability_probability_unique_internal_minimum_quartic_pos p
        exact False.elim (ne_of_gt hpos hquartic)
    · intro hp
      rw [hp]
      ring
  · dsimp [conclusion_window6_stability_probability_unique_internal_minimum_comparison_certificate,
      conclusion_window6_stability_probability_unique_internal_minimum_polynomial,
      conclusion_window6_stability_probability_unique_internal_minimum_pstar]
    norm_num
  · refine ⟨conclusion_window6_stability_probability_unique_internal_minimum_pstar, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · norm_num [conclusion_window6_stability_probability_unique_internal_minimum_pstar]
      · intro q _hq0 _hq1
        exact conclusion_window6_stability_probability_unique_internal_minimum_lower_bound q
      · norm_num [conclusion_window6_stability_probability_unique_internal_minimum_polynomial,
          conclusion_window6_stability_probability_unique_internal_minimum_pstar]
      · norm_num [conclusion_window6_stability_probability_unique_internal_minimum_polynomial,
          conclusion_window6_stability_probability_unique_internal_minimum_pstar]
      · norm_num [conclusion_window6_stability_probability_unique_internal_minimum_polynomial,
          conclusion_window6_stability_probability_unique_internal_minimum_pstar]
    · intro y hy
      have hle_pstar :
          conclusion_window6_stability_probability_unique_internal_minimum_polynomial y ≤
            conclusion_window6_stability_probability_unique_internal_minimum_polynomial
              conclusion_window6_stability_probability_unique_internal_minimum_pstar := by
        exact hy.2.1 conclusion_window6_stability_probability_unique_internal_minimum_pstar
          (by norm_num [conclusion_window6_stability_probability_unique_internal_minimum_pstar])
          (by norm_num [conclusion_window6_stability_probability_unique_internal_minimum_pstar])
      have hpstar_le :
          conclusion_window6_stability_probability_unique_internal_minimum_polynomial
              conclusion_window6_stability_probability_unique_internal_minimum_pstar ≤
            conclusion_window6_stability_probability_unique_internal_minimum_polynomial y :=
        conclusion_window6_stability_probability_unique_internal_minimum_lower_bound y
      have heq :
          conclusion_window6_stability_probability_unique_internal_minimum_polynomial y =
            conclusion_window6_stability_probability_unique_internal_minimum_polynomial
              conclusion_window6_stability_probability_unique_internal_minimum_pstar :=
        le_antisymm hle_pstar hpstar_le
      exact conclusion_window6_stability_probability_unique_internal_minimum_eq_pstar_of_eq heq

end

end Omega.Conclusion
