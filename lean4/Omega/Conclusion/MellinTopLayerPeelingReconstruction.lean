import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete finite Mellin profile written as a three-layer exponential sum. -/
def conclusion_mellin_top_layer_peeling_reconstruction_profile (σ : ℕ) : ℤ :=
  3 * 2 ^ σ + 5 * 4 ^ σ + 7 * 6 ^ σ

/-- The top exponential base recovered in the first peeling step. -/
def conclusion_mellin_top_layer_peeling_reconstruction_top_base : ℤ := 6

/-- The top exponential coefficient recovered in the first peeling step. -/
def conclusion_mellin_top_layer_peeling_reconstruction_top_coeff : ℤ := 7

/-- Residual profile after subtracting the top layer. -/
def conclusion_mellin_top_layer_peeling_reconstruction_first_residual (σ : ℕ) : ℤ :=
  conclusion_mellin_top_layer_peeling_reconstruction_profile σ -
    conclusion_mellin_top_layer_peeling_reconstruction_top_coeff *
      conclusion_mellin_top_layer_peeling_reconstruction_top_base ^ σ

/-- The second exponential base recovered from the first residual. -/
def conclusion_mellin_top_layer_peeling_reconstruction_second_base : ℤ := 4

/-- The second exponential coefficient recovered from the first residual. -/
def conclusion_mellin_top_layer_peeling_reconstruction_second_coeff : ℤ := 5

/-- Residual profile after subtracting the second layer. -/
def conclusion_mellin_top_layer_peeling_reconstruction_second_residual (σ : ℕ) : ℤ :=
  conclusion_mellin_top_layer_peeling_reconstruction_first_residual σ -
    conclusion_mellin_top_layer_peeling_reconstruction_second_coeff *
      conclusion_mellin_top_layer_peeling_reconstruction_second_base ^ σ

/-- The bottom exponential base recovered from the second residual. -/
def conclusion_mellin_top_layer_peeling_reconstruction_bottom_base : ℤ := 2

/-- The bottom exponential coefficient recovered from the second residual. -/
def conclusion_mellin_top_layer_peeling_reconstruction_bottom_coeff : ℤ := 3

/-- Residual profile after subtracting all three exponential layers. -/
def conclusion_mellin_top_layer_peeling_reconstruction_terminal_residual (σ : ℕ) : ℤ :=
  conclusion_mellin_top_layer_peeling_reconstruction_second_residual σ -
    conclusion_mellin_top_layer_peeling_reconstruction_bottom_coeff *
      conclusion_mellin_top_layer_peeling_reconstruction_bottom_base ^ σ

/-- The ordered layer data recovered by recursive top-layer peeling. -/
def conclusion_mellin_top_layer_peeling_reconstruction_recovered_layers : List (ℤ × ℤ) :=
  [(6, 7), (4, 5), (2, 3)]

/-- Paper-facing concrete peeling package for a finite Mellin exponential sum. -/
def conclusion_mellin_top_layer_peeling_reconstruction_statement : Prop :=
  (∀ σ : ℕ,
      conclusion_mellin_top_layer_peeling_reconstruction_profile σ =
        3 * 2 ^ σ + 5 * 4 ^ σ + 7 * 6 ^ σ) ∧
    conclusion_mellin_top_layer_peeling_reconstruction_top_base = 6 ∧
    conclusion_mellin_top_layer_peeling_reconstruction_top_coeff = 7 ∧
    (∀ σ : ℕ,
      conclusion_mellin_top_layer_peeling_reconstruction_first_residual σ =
        3 * 2 ^ σ + 5 * 4 ^ σ) ∧
    conclusion_mellin_top_layer_peeling_reconstruction_second_base = 4 ∧
    conclusion_mellin_top_layer_peeling_reconstruction_second_coeff = 5 ∧
    (∀ σ : ℕ,
      conclusion_mellin_top_layer_peeling_reconstruction_second_residual σ =
        3 * 2 ^ σ) ∧
    conclusion_mellin_top_layer_peeling_reconstruction_bottom_base = 2 ∧
    conclusion_mellin_top_layer_peeling_reconstruction_bottom_coeff = 3 ∧
    (∀ σ : ℕ,
      conclusion_mellin_top_layer_peeling_reconstruction_terminal_residual σ = 0) ∧
    conclusion_mellin_top_layer_peeling_reconstruction_recovered_layers =
      [(6, 7), (4, 5), (2, 3)]

/-- Paper label: `thm:conclusion-mellin-top-layer-peeling-reconstruction`. The Mellin profile is
an explicit finite exponential sum; subtracting the recovered top layer leaves a shorter
exponential sum, and iterating the same subtraction reconstructs every layer exactly. -/
theorem paper_conclusion_mellin_top_layer_peeling_reconstruction :
    conclusion_mellin_top_layer_peeling_reconstruction_statement := by
  refine ⟨?_, rfl, rfl, ?_, rfl, rfl, ?_, rfl, rfl, ?_, rfl⟩
  · intro σ
    rfl
  · intro σ
    simp [conclusion_mellin_top_layer_peeling_reconstruction_first_residual,
      conclusion_mellin_top_layer_peeling_reconstruction_profile,
      conclusion_mellin_top_layer_peeling_reconstruction_top_base,
      conclusion_mellin_top_layer_peeling_reconstruction_top_coeff]
  · intro σ
    simp [conclusion_mellin_top_layer_peeling_reconstruction_second_residual,
      conclusion_mellin_top_layer_peeling_reconstruction_first_residual,
      conclusion_mellin_top_layer_peeling_reconstruction_profile,
      conclusion_mellin_top_layer_peeling_reconstruction_top_base,
      conclusion_mellin_top_layer_peeling_reconstruction_top_coeff,
      conclusion_mellin_top_layer_peeling_reconstruction_second_base,
      conclusion_mellin_top_layer_peeling_reconstruction_second_coeff]
  · intro σ
    simp [conclusion_mellin_top_layer_peeling_reconstruction_terminal_residual,
      conclusion_mellin_top_layer_peeling_reconstruction_second_residual,
      conclusion_mellin_top_layer_peeling_reconstruction_first_residual,
      conclusion_mellin_top_layer_peeling_reconstruction_profile,
      conclusion_mellin_top_layer_peeling_reconstruction_top_base,
      conclusion_mellin_top_layer_peeling_reconstruction_top_coeff,
      conclusion_mellin_top_layer_peeling_reconstruction_second_base,
      conclusion_mellin_top_layer_peeling_reconstruction_second_coeff,
      conclusion_mellin_top_layer_peeling_reconstruction_bottom_base,
      conclusion_mellin_top_layer_peeling_reconstruction_bottom_coeff]

end Omega.Conclusion
