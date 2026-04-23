import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The diagonal feasibility threshold for the uniform `n`-point law. -/
def pom_diagonal_rate_uniform_closed_form_threshold (n : ℕ) : ℝ :=
  1 - 1 / (n : ℝ)

/-- Diagonal weight of the permutation-invariant coupling with total off-diagonal mass `δ`. -/
def pom_diagonal_rate_uniform_closed_form_diag_mass (n : ℕ) (δ : ℝ) : ℝ :=
  (1 - δ) / (n : ℝ)

/-- Off-diagonal weight of the permutation-invariant coupling with total off-diagonal mass `δ`. -/
def pom_diagonal_rate_uniform_closed_form_offdiag_mass (n : ℕ) (δ : ℝ) : ℝ :=
  δ / ((n : ℝ) * ((n : ℝ) - 1))

/-- Mutual information of the permutation-invariant uniform coupling with diagonal/off-diagonal
weights `a` and `b`, written against the product-uniform reference measure `1 / n^2`. -/
noncomputable def pom_diagonal_rate_uniform_closed_form_mutual_information
    (n : ℕ) (a b : ℝ) : ℝ :=
  (n : ℝ) * a * Real.log (a / (1 / (n : ℝ) ^ 2)) +
    ((n : ℝ) * ((n : ℝ) - 1)) * b * Real.log (b / (1 / (n : ℝ) ^ 2))

/-- Paper-facing closed form: below the threshold, the permutation-invariant feasible coupling with
diagonal mass `1 - δ` is uniquely determined by its diagonal and off-diagonal constants, and its
mutual information reduces to the stated scalar expression. At the threshold, the independent
coupling has zero mutual information. -/
def pomDiagonalRateUniformClosedForm : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃δ : ℝ⦄, 2 ≤ n → 0 ≤ δ → δ ≤ 1 →
    let δ0 := pom_diagonal_rate_uniform_closed_form_threshold n
    let a := pom_diagonal_rate_uniform_closed_form_diag_mass n δ
    let b := pom_diagonal_rate_uniform_closed_form_offdiag_mass n δ
    (δ < δ0 →
        (n : ℝ) * a = 1 - δ ∧
          ((n : ℝ) * ((n : ℝ) - 1)) * b = δ ∧
          (∀ a' b' : ℝ,
            (n : ℝ) * a' = 1 - δ →
              ((n : ℝ) * ((n : ℝ) - 1)) * b' = δ →
                a' = a ∧ b' = b) ∧
          pom_diagonal_rate_uniform_closed_form_mutual_information n a b =
            (1 - δ) * Real.log ((n : ℝ) * (1 - δ)) +
              δ * Real.log (δ * (n : ℝ) / ((n : ℝ) - 1))) ∧
      (pom_diagonal_rate_uniform_closed_form_mutual_information n
          (1 / (n : ℝ) ^ 2) (1 / (n : ℝ) ^ 2) = 0)

/-- The permutation-invariant coupling for the uniform law is uniquely pinned down by the diagonal
mass constraint, and its mutual information has the explicit two-term closed form.
    thm:pom-diagonal-rate-uniform-closed-form -/
theorem paper_pom_diagonal_rate_uniform_closed_form : pomDiagonalRateUniformClosedForm := by
  intro n δ hn hδ0 hδ1
  dsimp [pom_diagonal_rate_uniform_closed_form_threshold,
    pom_diagonal_rate_uniform_closed_form_diag_mass,
    pom_diagonal_rate_uniform_closed_form_offdiag_mass]
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hn1_ne : (n : ℝ) - 1 ≠ 0 := by
    have hn_gt : (1 : ℝ) < n := by
      exact_mod_cast (show 1 < n by omega)
    linarith
  have hnn_ne : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := mul_ne_zero hn_ne hn1_ne
  refine ⟨?_, ?_⟩
  · intro hδlt
    refine ⟨?_, ?_, ?_, ?_⟩
    · field_simp [hn_ne]
    · field_simp [hnn_ne]
    · intro a' b' ha' hb'
      constructor
      · apply (eq_div_iff hn_ne).2
        linarith
      · apply (eq_div_iff hnn_ne).2
        linarith
    · unfold pom_diagonal_rate_uniform_closed_form_mutual_information
      have hcoeff_diag : (n : ℝ) * ((1 - δ) / (n : ℝ)) = 1 - δ := by
        field_simp [hn_ne]
      have hcoeff_off :
          ((n : ℝ) * ((n : ℝ) - 1)) * (δ / ((n : ℝ) * ((n : ℝ) - 1))) = δ := by
        field_simp [hn_ne, hn1_ne]
      have hdiag :
          ((1 - δ) / (n : ℝ)) / (1 / (n : ℝ) ^ 2) = (n : ℝ) * (1 - δ) := by
        field_simp [hn_ne]
      have hoff :
          (δ / ((n : ℝ) * ((n : ℝ) - 1))) / (1 / (n : ℝ) ^ 2) =
            δ * (n : ℝ) / ((n : ℝ) - 1) := by
        field_simp [hn_ne, hn1_ne]
      rw [hcoeff_diag, hcoeff_off, hdiag, hoff]
  · unfold pom_diagonal_rate_uniform_closed_form_mutual_information
    have hpow_ne : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hn_ne
    simp [hpow_ne]

end

end Omega.POM
