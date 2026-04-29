import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the Toeplitz-margin threshold law: a subunit decay, a positive
normalization, a real threshold exponent, and the observed extremal norms. -/
structure conclusion_toeplitz_margin_sharp_threshold_law_data where
  conclusion_toeplitz_margin_sharp_threshold_law_decay : ℝ
  conclusion_toeplitz_margin_sharp_threshold_law_decay_pos :
    0 < conclusion_toeplitz_margin_sharp_threshold_law_decay
  conclusion_toeplitz_margin_sharp_threshold_law_decay_lt_one :
    conclusion_toeplitz_margin_sharp_threshold_law_decay < 1
  conclusion_toeplitz_margin_sharp_threshold_law_amplitude : ℝ
  conclusion_toeplitz_margin_sharp_threshold_law_amplitude_pos :
    0 < conclusion_toeplitz_margin_sharp_threshold_law_amplitude
  conclusion_toeplitz_margin_sharp_threshold_law_exponent : ℝ
  conclusion_toeplitz_margin_sharp_threshold_law_threshold_order : ℕ
  conclusion_toeplitz_margin_sharp_threshold_law_threshold_order_eq_ceil :
    conclusion_toeplitz_margin_sharp_threshold_law_threshold_order =
      Nat.ceil conclusion_toeplitz_margin_sharp_threshold_law_exponent
  conclusion_toeplitz_margin_sharp_threshold_law_norm : ℕ → ℝ

namespace conclusion_toeplitz_margin_sharp_threshold_law_data

/-- The extremal norm profile supplied by the sharp Toeplitz margin computation. -/
noncomputable def conclusion_toeplitz_margin_sharp_threshold_law_model_norm
    (D : conclusion_toeplitz_margin_sharp_threshold_law_data) (n : ℕ) : ℝ :=
  D.conclusion_toeplitz_margin_sharp_threshold_law_amplitude *
    D.conclusion_toeplitz_margin_sharp_threshold_law_decay ^ (n : ℝ)

/-- The sharp margin level at the real threshold exponent. -/
noncomputable def conclusion_toeplitz_margin_sharp_threshold_law_margin
    (D : conclusion_toeplitz_margin_sharp_threshold_law_data) : ℝ :=
  D.conclusion_toeplitz_margin_sharp_threshold_law_amplitude *
    D.conclusion_toeplitz_margin_sharp_threshold_law_decay ^
      D.conclusion_toeplitz_margin_sharp_threshold_law_exponent

end conclusion_toeplitz_margin_sharp_threshold_law_data

open conclusion_toeplitz_margin_sharp_threshold_law_data

/-- The extremal norm identity with the subunit Toeplitz decay. -/
def conclusion_toeplitz_margin_sharp_threshold_law_extremal_norm
    (D : conclusion_toeplitz_margin_sharp_threshold_law_data) : Prop :=
  ∀ n : ℕ,
    D.conclusion_toeplitz_margin_sharp_threshold_law_norm n =
      D.conclusion_toeplitz_margin_sharp_threshold_law_model_norm n

/-- The threshold law: the norm inequality is equivalent to passing the real exponent, and
the minimal integer order is its natural ceiling. -/
def conclusion_toeplitz_margin_sharp_threshold_law_threshold_formula
    (D : conclusion_toeplitz_margin_sharp_threshold_law_data) : Prop :=
  (∀ n : ℕ,
    D.conclusion_toeplitz_margin_sharp_threshold_law_norm n ≤
        D.conclusion_toeplitz_margin_sharp_threshold_law_margin ↔
      D.conclusion_toeplitz_margin_sharp_threshold_law_exponent ≤ (n : ℝ)) ∧
  (∀ n : ℕ,
    D.conclusion_toeplitz_margin_sharp_threshold_law_threshold_order ≤ n ↔
      D.conclusion_toeplitz_margin_sharp_threshold_law_exponent ≤ (n : ℝ)) ∧
  (∀ n : ℕ,
    D.conclusion_toeplitz_margin_sharp_threshold_law_norm n ≤
        D.conclusion_toeplitz_margin_sharp_threshold_law_margin ↔
      D.conclusion_toeplitz_margin_sharp_threshold_law_threshold_order ≤ n)

/-- Paper label: `thm:conclusion-toeplitz-margin-sharp-threshold-law`. -/
theorem paper_conclusion_toeplitz_margin_sharp_threshold_law
    (D : conclusion_toeplitz_margin_sharp_threshold_law_data) :
    conclusion_toeplitz_margin_sharp_threshold_law_extremal_norm D →
      conclusion_toeplitz_margin_sharp_threshold_law_threshold_formula D := by
  intro hnorm
  let norm_threshold : ∀ n : ℕ,
      D.conclusion_toeplitz_margin_sharp_threshold_law_norm n ≤
          D.conclusion_toeplitz_margin_sharp_threshold_law_margin ↔
        D.conclusion_toeplitz_margin_sharp_threshold_law_exponent ≤ (n : ℝ) := by
    intro n
    rw [hnorm n, conclusion_toeplitz_margin_sharp_threshold_law_model_norm,
      conclusion_toeplitz_margin_sharp_threshold_law_margin]
    rw [mul_le_mul_iff_right₀
      D.conclusion_toeplitz_margin_sharp_threshold_law_amplitude_pos]
    exact Real.rpow_le_rpow_left_iff_of_base_lt_one
      D.conclusion_toeplitz_margin_sharp_threshold_law_decay_pos
      D.conclusion_toeplitz_margin_sharp_threshold_law_decay_lt_one
  let ceil_threshold : ∀ n : ℕ,
      D.conclusion_toeplitz_margin_sharp_threshold_law_threshold_order ≤ n ↔
        D.conclusion_toeplitz_margin_sharp_threshold_law_exponent ≤ (n : ℝ) := by
    intro n
    rw [D.conclusion_toeplitz_margin_sharp_threshold_law_threshold_order_eq_ceil]
    exact Nat.ceil_le
  refine ⟨norm_threshold, ceil_threshold, ?_⟩
  intro n
  constructor
  · intro hn
    exact (ceil_threshold n).2 ((norm_threshold n).1 hn)
  · intro hn
    exact (norm_threshold n).2 ((ceil_threshold n).1 hn)

end Omega.Conclusion
