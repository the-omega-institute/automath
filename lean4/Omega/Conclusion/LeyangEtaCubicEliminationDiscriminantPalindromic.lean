import Mathlib.Tactic

namespace Omega.Conclusion

/-- The `a` coefficient of the Lee--Yang eta cubic. -/
def conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_a (η : ℤ) : ℤ :=
  64 * (η - 1) ^ 2

/-- The `b` coefficient of the Lee--Yang eta cubic. -/
def conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_b (η : ℤ) : ℤ :=
  3 * (32 * η ^ 2 - 73 * η + 32)

/-- The `c` coefficient of the Lee--Yang eta cubic. -/
def conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_c (η : ℤ) : ℤ :=
  3 * (16 * η ^ 2 - 23 * η + 16)

/-- The `d` coefficient of the Lee--Yang eta cubic. -/
def conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_d (η : ℤ) : ℤ :=
  8 * (η - 1) ^ 2

/-- The eta cubic polynomial evaluated at `y`. -/
def conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_cubic
    (η y : ℤ) : ℤ :=
  conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_a η * y ^ 3 +
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_b η * y ^ 2 +
      conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_c η * y +
        conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_d η

/-- The palindromic quartic factor in the cubic discriminant. -/
def conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_D (η : ℤ) : ℤ :=
  2304 * η ^ 4 - 8896 * η ^ 3 + 13157 * η ^ 2 - 8896 * η + 2304

/-- The same quartic over the rationals, used for the reciprocal identity. -/
def conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_D_rat (η : ℚ) : ℚ :=
  2304 * η ^ 4 - 8896 * η ^ 3 + 13157 * η ^ 2 - 8896 * η + 2304

/-- The discriminant of the eta cubic, written using the standard cubic formula. -/
def conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_disc (η : ℤ) : ℤ :=
  let a := conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_a η
  let b := conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_b η
  let c := conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_c η
  let d := conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_d η
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 +
    18 * a * b * c * d

/-- The expanded cubic identity with the prefixed coefficient package. -/
def conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_cubic_identity :
    Prop :=
  ∀ η y : ℤ,
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_cubic η y =
      64 * (η - 1) ^ 2 * y ^ 3 +
        3 * (32 * η ^ 2 - 73 * η + 32) * y ^ 2 +
          3 * (16 * η ^ 2 - 23 * η + 16) * y +
            8 * (η - 1) ^ 2

/-- The discriminant factorization of the eta cubic. -/
def conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_disc_factorization :
    Prop :=
  ∀ η : ℤ,
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_disc η =
      -(3 ^ 9) * η ^ 2 *
        conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_D η

/-- The quartic factor is self-reciprocal. -/
def conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_self_reciprocal :
    Prop :=
  ∀ η : ℚ, η ≠ 0 →
    η ^ 4 *
        conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_D_rat η⁻¹ =
      conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_D_rat η

private lemma conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_cubic_identity_proof :
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_cubic_identity := by
  intro η y
  unfold conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_cubic
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_a
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_b
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_c
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_d
  ring

private lemma conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_disc_factorization_proof :
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_disc_factorization := by
  intro η
  unfold conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_disc
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_a
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_b
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_c
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_d
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_D
  ring

private lemma conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_self_reciprocal_proof :
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_self_reciprocal := by
  intro η hη
  unfold conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_D_rat
  field_simp [hη]
  ring

/-- Paper label: `thm:conclusion-leyang-eta-cubic-elimination-discriminant-palindromic`. -/
theorem paper_conclusion_leyang_eta_cubic_elimination_discriminant_palindromic :
    conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_cubic_identity ∧
      conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_disc_factorization ∧
      conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_self_reciprocal := by
  exact
    ⟨conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_cubic_identity_proof,
      conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_disc_factorization_proof,
      conclusion_leyang_eta_cubic_elimination_discriminant_palindromic_self_reciprocal_proof⟩

end Omega.Conclusion
