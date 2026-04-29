import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Sitewise hidden generating factor for the three local window-6 laws. -/
def conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_factor
    (d : ℕ) (u v : ℂ) : ℂ :=
  match d with
  | 2 => 1 + v
  | 3 => 1 + u + v
  | 4 => (1 + u) * (1 + v)
  | _ => 1

/-- Product hidden generating polynomial for a finite visible background. -/
def conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_product
    {n : ℕ} (d : Fin n → ℕ) (u v : Fin n → ℂ) : ℂ :=
  ∏ x : Fin n,
    conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_factor
      (d x) (u x) (v x)

/-- Real-stability nonvanishing statement on the product of local factors. -/
def conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_real_stable
    {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∀ u v : Fin n → ℂ,
    (∀ x, 0 < (u x).im) →
      (∀ x, 0 < (v x).im) →
        conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_product
          d u v ≠ 0

/-- The abstract local odd coefficient; only the `d = 3` layer is allowed to survive. -/
def conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_local_odd
    (d m : ℕ) : ℝ :=
  if d = 3 then ((m + 1 : ℕ) : ℝ) else 0

/-- The finite-product odd cumulant after sitewise additivity. -/
def conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_global_odd
    {n : ℕ} (d : Fin n → ℕ) (a : Fin n → ℝ) (m : ℕ) : ℝ :=
  ∑ x : Fin n,
    a x ^ (2 * m + 1) *
      conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_local_odd
        (d x) m

/-- The localized odd cumulant supported on the `d = 3` layer. -/
def conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_localized_odd
    {n : ℕ} (d : Fin n → ℕ) (a : Fin n → ℝ) (m : ℕ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin n => d x = 3),
    a x ^ (2 * m + 1) * ((m + 1 : ℕ) : ℝ)

/-- The centered `d = 3` local third cumulant, computed from the three atoms. -/
def conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_d3_third :
    ℝ :=
  (((-55 / 3 : ℝ) ^ 3 + (8 / 3 : ℝ) ^ 3 + (47 / 3 : ℝ) ^ 3) / 3)

/-- The third cumulant of the finite product law. -/
def conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_global_third
    {n : ℕ} (d : Fin n → ℕ) (a : Fin n → ℝ) : ℝ :=
  ∑ x : Fin n,
    a x ^ 3 *
      if d x = 3 then
        conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_d3_third
      else
        0

/-- Concrete statement of real stability and odd-cumulant localization. -/
def conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_statement :
    Prop :=
  (∀ {n : ℕ} (d : Fin n → ℕ),
    conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_real_stable d) ∧
    (∀ {n : ℕ} (d : Fin n → ℕ) (a : Fin n → ℝ) (m : ℕ),
      conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_global_odd d a m =
        conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_localized_odd
          d a m) ∧
      conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_d3_third =
        -20680 / 27 ∧
        (∀ {n : ℕ} (d : Fin n → ℕ) (a : Fin n → ℝ),
          conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_global_third d a =
            (-20680 / 27 : ℝ) *
              ∑ x ∈ Finset.univ.filter (fun x : Fin n => d x = 3), a x ^ 3)

private lemma conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_factor_ne_zero
  (d : ℕ) {u v : ℂ} (hu : 0 < u.im) (hv : 0 < v.im) :
    conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_factor d u v ≠ 0 := by
  by_cases h2 : d = 2
  · subst d
    simp [conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_factor]
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  by_cases h3 : d = 3
  · subst d
    simp [conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_factor]
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  by_cases h4 : d = 4
  · subst d
    have hu1 : (1 + u : ℂ) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hv1 : (1 + v : ℂ) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp at him
      linarith
    simp [conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_factor,
      hu1, hv1]
  · simp [conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_factor]

private lemma conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_d3_third_eval :
    conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_d3_third =
      -20680 / 27 := by
  norm_num [conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_d3_third]

/-- Paper label: `thm:conclusion-window6-hidden-realstable-d2slice-odd-cumulant-localization`. -/
theorem paper_conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization :
    conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_statement := by
  unfold conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_statement
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n d u v hu hv
    unfold conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_product
    rw [Finset.prod_ne_zero_iff]
    intro x hx
    exact
      conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_factor_ne_zero
        (d x) (hu x) (hv x)
  · intro n d a m
    unfold conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_global_odd
      conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_localized_odd
      conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_local_odd
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : d x = 3 <;> simp [h]
  · exact conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_d3_third_eval
  · intro n d a
    unfold conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_global_third
    rw [conclusion_window6_hidden_realstable_d2slice_odd_cumulant_localization_d3_third_eval]
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : d x = 3 <;> simp [h]
    ring

end

end Omega.Conclusion
