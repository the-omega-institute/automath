import Mathlib.Tactic

namespace Omega.Conclusion

/-- The normalized two-fiber Renyi moment in the concrete `α = 3` stability model. -/
noncomputable def conclusion_twofiber_renyi_stability_balance_normalizedMoment (δ : ℝ) : ℝ :=
  4 / (1 - δ ^ 2)

/-- The quadratic stability lower bound for the concrete two-fiber moment. -/
def conclusion_twofiber_renyi_stability_balance_renyi_moment_lower_bound
    (δ : ℝ) : Prop :=
  conclusion_twofiber_renyi_stability_balance_normalizedMoment δ ≥ 4 * (1 + δ ^ 2)

/-- Equality in the lower bound occurs exactly at balanced fibers. -/
def conclusion_twofiber_renyi_stability_balance_equality_iff_balanced (δ : ℝ) : Prop :=
  conclusion_twofiber_renyi_stability_balance_normalizedMoment δ = 4 * (1 + δ ^ 2) ↔
    δ = 0

/-- Paper label: `prop:conclusion-twofiber-renyi-stability-balance`. -/
theorem paper_conclusion_twofiber_renyi_stability_balance (δ : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hδ_lt_one : δ < 1) :
    conclusion_twofiber_renyi_stability_balance_renyi_moment_lower_bound δ ∧
      conclusion_twofiber_renyi_stability_balance_equality_iff_balanced δ := by
  have hδ_sq_nonneg : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hδ_sq_lt_one : δ ^ 2 < 1 := by
    nlinarith [hδ_nonneg, hδ_lt_one]
  have hden_pos : 0 < 1 - δ ^ 2 := by
    nlinarith
  constructor
  · rw [conclusion_twofiber_renyi_stability_balance_renyi_moment_lower_bound,
      conclusion_twofiber_renyi_stability_balance_normalizedMoment]
    change 4 * (1 + δ ^ 2) ≤ 4 / (1 - δ ^ 2)
    rw [le_div_iff₀ hden_pos]
    nlinarith [sq_nonneg (δ ^ 2)]
  · rw [conclusion_twofiber_renyi_stability_balance_equality_iff_balanced,
      conclusion_twofiber_renyi_stability_balance_normalizedMoment]
    constructor
    · intro h
      have hmul := congrArg (fun x : ℝ => x * (1 - δ ^ 2)) h
      field_simp [hden_pos.ne'] at hmul
      ring_nf at hmul
      have hsq : δ ^ 2 = 0 := by
        nlinarith [sq_nonneg (δ ^ 2)]
      exact sq_eq_zero_iff.mp hsq
    · intro h
      simp [h]

end Omega.Conclusion
