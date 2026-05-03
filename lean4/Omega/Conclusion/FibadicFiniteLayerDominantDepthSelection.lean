import Mathlib

namespace Omega.Conclusion

open Filter

/-- Three finite diagonal blocks for the seed finite-layer fibadic model. -/
abbrev conclusion_fibadic_finite_layer_dominant_depth_selection_block := Fin 3

/-- The unique dominant scalar is on block `0`; the two other blocks are nil in this seed layer. -/
def conclusion_fibadic_finite_layer_dominant_depth_selection_scalar
    (b : conclusion_fibadic_finite_layer_dominant_depth_selection_block) : ℚ :=
  if b = 0 then 2 else 0

/-- Dominant scalar used to normalize all powers. -/
def conclusion_fibadic_finite_layer_dominant_depth_selection_dominant_scalar : ℚ :=
  2

/-- Normalized block power after dividing by the dominant scalar power. -/
def conclusion_fibadic_finite_layer_dominant_depth_selection_normalized_power
    (n : ℕ) (b : conclusion_fibadic_finite_layer_dominant_depth_selection_block) : ℚ :=
  conclusion_fibadic_finite_layer_dominant_depth_selection_scalar b ^ (n + 1) /
    conclusion_fibadic_finite_layer_dominant_depth_selection_dominant_scalar ^ (n + 1)

/-- Finite supremum norm of the non-dominant normalized block powers. -/
def conclusion_fibadic_finite_layer_dominant_depth_selection_finite_sup_norm (n : ℕ) : ℚ :=
  max
    |conclusion_fibadic_finite_layer_dominant_depth_selection_normalized_power n 1|
    |conclusion_fibadic_finite_layer_dominant_depth_selection_normalized_power n 2|

/-- Concrete paper-facing statement: the dominant block stays normalized to `1`, every
non-dominant block ratio vanishes, and therefore the finite supremum norm tends to `0`. -/
def conclusion_fibadic_finite_layer_dominant_depth_selection_statement : Prop :=
  (∀ n,
    conclusion_fibadic_finite_layer_dominant_depth_selection_normalized_power n 0 = 1) ∧
    (∀ n b, b ≠ 0 →
      conclusion_fibadic_finite_layer_dominant_depth_selection_normalized_power n b = 0) ∧
      Tendsto conclusion_fibadic_finite_layer_dominant_depth_selection_finite_sup_norm
        atTop (nhds 0)

private lemma conclusion_fibadic_finite_layer_dominant_depth_selection_dominant_power
    (n : ℕ) :
    conclusion_fibadic_finite_layer_dominant_depth_selection_normalized_power n 0 = 1 := by
  simp [conclusion_fibadic_finite_layer_dominant_depth_selection_normalized_power,
    conclusion_fibadic_finite_layer_dominant_depth_selection_scalar,
    conclusion_fibadic_finite_layer_dominant_depth_selection_dominant_scalar]

private lemma conclusion_fibadic_finite_layer_dominant_depth_selection_nondominant_power
    (n : ℕ) (b : conclusion_fibadic_finite_layer_dominant_depth_selection_block)
    (hb : b ≠ 0) :
    conclusion_fibadic_finite_layer_dominant_depth_selection_normalized_power n b = 0 := by
  simp [conclusion_fibadic_finite_layer_dominant_depth_selection_normalized_power,
    conclusion_fibadic_finite_layer_dominant_depth_selection_scalar,
    conclusion_fibadic_finite_layer_dominant_depth_selection_dominant_scalar, hb]

private lemma conclusion_fibadic_finite_layer_dominant_depth_selection_sup_norm_zero
    (n : ℕ) :
    conclusion_fibadic_finite_layer_dominant_depth_selection_finite_sup_norm n = 0 := by
  simp [conclusion_fibadic_finite_layer_dominant_depth_selection_finite_sup_norm,
    conclusion_fibadic_finite_layer_dominant_depth_selection_nondominant_power]

/-- Paper label:
`thm:conclusion-fibadic-finite-layer-dominant-depth-selection`. -/
theorem paper_conclusion_fibadic_finite_layer_dominant_depth_selection :
    conclusion_fibadic_finite_layer_dominant_depth_selection_statement := by
  refine ⟨conclusion_fibadic_finite_layer_dominant_depth_selection_dominant_power, ?_, ?_⟩
  · exact conclusion_fibadic_finite_layer_dominant_depth_selection_nondominant_power
  · have hfun :
        conclusion_fibadic_finite_layer_dominant_depth_selection_finite_sup_norm =
          fun _ : ℕ => (0 : ℚ) := by
      funext n
      exact conclusion_fibadic_finite_layer_dominant_depth_selection_sup_norm_zero n
    rw [hfun]
    exact tendsto_const_nhds

end Omega.Conclusion
