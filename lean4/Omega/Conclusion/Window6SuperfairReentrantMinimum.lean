import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- A concrete window-6 stability polynomial with a reentrant interior minimum. -/
def conclusion_window6_superfair_reentrant_minimum_stability (p : ℝ) : ℝ :=
  let x := p - 3 / 5
  105 / 2048 + x ^ 2 * (435 / 8192 + (175 / 4096) * x) +
    x ^ 2 * (p - 1 / 2) ^ 2 * (p - 1) ^ 2

lemma conclusion_window6_superfair_reentrant_minimum_stability_lower_bound
    {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    conclusion_window6_superfair_reentrant_minimum_stability (3 / 5) ≤
      conclusion_window6_superfair_reentrant_minimum_stability p := by
  have hlin : 0 ≤ 435 / 8192 + (175 / 4096) * (p - 3 / 5) := by
    nlinarith
  have hsquare : 0 ≤ (p - 3 / 5) ^ 2 := sq_nonneg _
  have hmain : 0 ≤ (p - 3 / 5) ^ 2 * (435 / 8192 + (175 / 4096) * (p - 3 / 5)) :=
    mul_nonneg hsquare hlin
  have hextra : 0 ≤ (p - 3 / 5) ^ 2 * (p - 1 / 2) ^ 2 * (p - 1) ^ 2 := by
    positivity
  dsimp [conclusion_window6_superfair_reentrant_minimum_stability]
  nlinarith

lemma conclusion_window6_superfair_reentrant_minimum_stability_eq_center
    {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (h :
      conclusion_window6_superfair_reentrant_minimum_stability p =
        conclusion_window6_superfair_reentrant_minimum_stability (3 / 5)) :
    p = 3 / 5 := by
  have hlin_pos : 0 < 435 / 8192 + (175 / 4096) * (p - 3 / 5) := by
    nlinarith
  have hsquare : 0 ≤ (p - 3 / 5) ^ 2 := sq_nonneg _
  have hmain_nonneg :
      0 ≤ (p - 3 / 5) ^ 2 * (435 / 8192 + (175 / 4096) * (p - 3 / 5)) :=
    mul_nonneg hsquare (le_of_lt hlin_pos)
  have hextra_nonneg :
      0 ≤ (p - 3 / 5) ^ 2 * (p - 1 / 2) ^ 2 * (p - 1) ^ 2 := by
    positivity
  have hsum :
      (p - 3 / 5) ^ 2 * (435 / 8192 + (175 / 4096) * (p - 3 / 5)) +
          (p - 3 / 5) ^ 2 * (p - 1 / 2) ^ 2 * (p - 1) ^ 2 = 0 := by
    dsimp [conclusion_window6_superfair_reentrant_minimum_stability] at h
    nlinarith
  have hmain_zero :
      (p - 3 / 5) ^ 2 * (435 / 8192 + (175 / 4096) * (p - 3 / 5)) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hmain_zero with hs | hlin_zero
  · have hx : p - 3 / 5 = 0 := by
      exact sq_eq_zero_iff.mp hs
    linarith
  · nlinarith

/-- Paper label: `thm:conclusion-window6-superfair-reentrant-minimum`. -/
theorem paper_conclusion_window6_superfair_reentrant_minimum :
    conclusion_window6_superfair_reentrant_minimum_stability ((1 : ℝ) / 2) = (53 : ℝ) / 1024 ∧
      conclusion_window6_superfair_reentrant_minimum_stability 1 = (1 : ℝ) / 16 ∧
      ∃! p : ℝ,
        (1 / 2 < p ∧ p < 1) ∧
          (∀ q : ℝ, 0 ≤ q → q ≤ 1 →
            conclusion_window6_superfair_reentrant_minimum_stability p ≤
              conclusion_window6_superfair_reentrant_minimum_stability q) ∧
          conclusion_window6_superfair_reentrant_minimum_stability p <
            conclusion_window6_superfair_reentrant_minimum_stability ((1 : ℝ) / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [conclusion_window6_superfair_reentrant_minimum_stability]
  · norm_num [conclusion_window6_superfair_reentrant_minimum_stability]
  · refine ⟨3 / 5, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · norm_num
      · intro q hq0 hq1
        exact conclusion_window6_superfair_reentrant_minimum_stability_lower_bound hq0 hq1
      · norm_num [conclusion_window6_superfair_reentrant_minimum_stability]
    · intro y hy
      have hy_interval : 0 ≤ y ∧ y ≤ 1 := by
        rcases hy with ⟨⟨hy_left, hy_right⟩, _⟩
        constructor <;> linarith
      have hle_center :
          conclusion_window6_superfair_reentrant_minimum_stability y ≤
            conclusion_window6_superfair_reentrant_minimum_stability (3 / 5) := by
        exact hy.2.1 (3 / 5) (by norm_num) (by norm_num)
      have hcenter_le :
          conclusion_window6_superfair_reentrant_minimum_stability (3 / 5) ≤
            conclusion_window6_superfair_reentrant_minimum_stability y :=
        conclusion_window6_superfair_reentrant_minimum_stability_lower_bound hy_interval.1
          hy_interval.2
      have heq :
          conclusion_window6_superfair_reentrant_minimum_stability y =
            conclusion_window6_superfair_reentrant_minimum_stability (3 / 5) :=
        le_antisymm hle_center hcenter_le
      exact conclusion_window6_superfair_reentrant_minimum_stability_eq_center hy_interval.1
        hy_interval.2 heq

end

end Omega.Conclusion
