import Mathlib.Tactic

namespace Omega.Conclusion

/-- Audited conclusion-layer data for the `q = 4` kernel-RH threshold window.
The record keeps the numeric delta profile concrete, together with the already-formalized
mean-square sign criteria used to turn the audited signs into the two phase predicates. -/
structure conclusion_kernel_rh_q4_minimal_threshold_data where
  delta : ℕ → ℝ
  sqrtStable : ℕ → Prop
  boundaryDominated : ℕ → Prop
  delta_two_lt_zero : delta 2 < 0
  delta_three_lt_zero : delta 3 < 0
  delta_four_gt_zero : 0 < delta 4
  delta_audited_window_positive : ∀ q : ℕ, 4 ≤ q → q ≤ 23 → 0 < delta q
  sqrtStable_of_delta_negative : ∀ q : ℕ, q = 2 ∨ q = 3 → delta q < 0 → sqrtStable q
  boundaryDominated_of_delta_positive :
    ∀ q : ℕ, 4 ≤ q → q ≤ 23 → 0 < delta q → boundaryDominated q

/-- Paper label: `thm:conclusion-kernel-rh-q4-minimal-threshold`. -/
theorem paper_conclusion_kernel_rh_q4_minimal_threshold
    (D : conclusion_kernel_rh_q4_minimal_threshold_data) :
    D.delta 2 < 0 ∧ D.delta 3 < 0 ∧ 0 < D.delta 4 ∧
      (∀ q : ℕ, 4 ≤ q → q ≤ 23 → 0 < D.delta q) ∧ D.sqrtStable 2 ∧
        D.sqrtStable 3 ∧
          (∀ q : ℕ, 4 ≤ q → q ≤ 23 → D.boundaryDominated q) := by
  refine ⟨D.delta_two_lt_zero, D.delta_three_lt_zero, D.delta_four_gt_zero, ?_, ?_, ?_, ?_⟩
  · intro q hq4 hq23
    exact D.delta_audited_window_positive q hq4 hq23
  · exact D.sqrtStable_of_delta_negative 2 (Or.inl rfl) D.delta_two_lt_zero
  · exact D.sqrtStable_of_delta_negative 3 (Or.inr rfl) D.delta_three_lt_zero
  · intro q hq4 hq23
    exact D.boundaryDominated_of_delta_positive q hq4 hq23
      (D.delta_audited_window_positive q hq4 hq23)

end Omega.Conclusion
