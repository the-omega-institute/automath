import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Folding.KilloLeyangTwoBranchFieldsProductGalois

namespace Omega.Folding

/-- The branch cubic in the `λ`-coordinate from the Lee--Yang audit. -/
def killo_leyang_kappa_square_cubic_field_branch_polynomial (lam : ℚ) : ℚ :=
  16 * lam ^ 3 - 9 * lam ^ 2 + 1

/-- The rational function `u = κ_*^2` written in terms of `λ`. -/
def killo_leyang_kappa_square_cubic_field_u_from_lambda (lam : ℚ) : ℚ :=
  2 * (3 * lam ^ 2 - 1) / (3 * (lam ^ 2 - 1))

/-- The recovered square `λ²` written in terms of `u`. -/
def killo_leyang_kappa_square_cubic_field_lambda_sq_from_u (u : ℚ) : ℚ :=
  (3 * u - 2) / (3 * (u - 2))

/-- The recovered branch parameter `λ` written in terms of `u`. -/
def killo_leyang_kappa_square_cubic_field_lambda_from_u (u : ℚ) : ℚ :=
  3 * (2 * u - 1) / (4 * (3 * u - 2))

/-- The eliminated cubic polynomial satisfied by `u = κ_*²`. -/
def killo_leyang_kappa_square_cubic_field_cubic (u : ℚ) : ℚ :=
  324 * u ^ 3 - 540 * u ^ 2 + 333 * u - 74

/-- Integer coefficient form of the cubic discriminant. -/
def killo_leyang_kappa_square_cubic_field_cubic_discriminant_formula
    (a b c d : ℤ) : ℤ :=
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d

/-- The discriminant of `324 u^3 - 540 u^2 + 333 u - 74`. -/
def killo_leyang_kappa_square_cubic_field_discriminant : ℤ :=
  killo_leyang_kappa_square_cubic_field_cubic_discriminant_formula 324 (-540) 333 (-74)

/-- The mod-`5` reduction of the eliminated cubic. -/
def killo_leyang_kappa_square_cubic_field_mod5 (u : ZMod 5) : ZMod 5 :=
  4 * u ^ 3 + 3 * u + 1

/-- The mod-`5` reduction has no root, giving the chapter-local irreducibility witness. -/
def killo_leyang_kappa_square_cubic_field_mod5_irreducible : Prop :=
  ∀ u : ZMod 5, killo_leyang_kappa_square_cubic_field_mod5 u ≠ 0

/-- Chapter-local `S₃` certificate for the cubic field. -/
def killo_leyang_kappa_square_cubic_field_galois_group_is_S3 : Prop :=
  killo_leyang_kappa_square_cubic_field_mod5_irreducible ∧
    ¬ IsSquare killo_leyang_kappa_square_cubic_field_discriminant

/-- Paper-facing Lee--Yang `κ_*²` cubic-field package. -/
def killo_leyang_kappa_square_cubic_field_statement : Prop :=
  (∀ lam : ℚ,
      killo_leyang_kappa_square_cubic_field_u_from_lambda lam =
        2 * (3 * lam ^ 2 - 1) / (3 * (lam ^ 2 - 1))) ∧
    (∀ u : ℚ,
      killo_leyang_kappa_square_cubic_field_lambda_from_u u =
        3 * (2 * u - 1) / (4 * (3 * u - 2))) ∧
    (∀ u : ℚ,
      killo_leyang_kappa_square_cubic_field_cubic u =
        324 * u ^ 3 - 540 * u ^ 2 + 333 * u - 74) ∧
    killo_leyang_kappa_square_cubic_field_discriminant =
      -((2 : ℤ) ^ 6 * (3 : ℤ) ^ 9 * 37) ∧
    killo_leyang_kappa_square_cubic_field_mod5_irreducible ∧
    ¬ IsSquare killo_leyang_kappa_square_cubic_field_discriminant ∧
    killoLeyangCubicQuadraticSubfieldDiscriminant = -111 ∧
    killo_leyang_kappa_square_cubic_field_galois_group_is_S3

private lemma killo_leyang_kappa_square_cubic_field_discriminant_eval :
    killo_leyang_kappa_square_cubic_field_discriminant =
      -((2 : ℤ) ^ 6 * (3 : ℤ) ^ 9 * 37) := by
  norm_num [killo_leyang_kappa_square_cubic_field_discriminant,
    killo_leyang_kappa_square_cubic_field_cubic_discriminant_formula]

private lemma killo_leyang_kappa_square_cubic_field_mod5_irreducible_true :
    killo_leyang_kappa_square_cubic_field_mod5_irreducible := by
  intro u
  fin_cases u <;> decide

private lemma killo_leyang_kappa_square_cubic_field_discriminant_not_square :
    ¬ IsSquare killo_leyang_kappa_square_cubic_field_discriminant := by
  intro hsquare
  rcases hsquare with ⟨n, hn⟩
  have hnonneg : 0 ≤ killo_leyang_kappa_square_cubic_field_discriminant := by
    simpa [pow_two, hn] using sq_nonneg n
  rw [killo_leyang_kappa_square_cubic_field_discriminant_eval] at hnonneg
  norm_num at hnonneg

/-- Paper label: `thm:killo-leyang-kappa-square-cubic-field`. Eliminating the Lee--Yang branch
parameter `λ` from the rational formula for `u = κ_*²` produces the cubic
`324 u^3 - 540 u^2 + 333 u - 74 = 0`. Its discriminant has squarefree kernel `-111`, matching the
chapter's cubic quadratic-subfield audit, and the mod-`5` irreducibility witness together with the
nonsquare discriminant provides the local `S₃` certificate. -/
theorem paper_killo_leyang_kappa_square_cubic_field :
    killo_leyang_kappa_square_cubic_field_statement := by
  refine ⟨?_, ?_, ?_, killo_leyang_kappa_square_cubic_field_discriminant_eval,
    killo_leyang_kappa_square_cubic_field_mod5_irreducible_true,
    killo_leyang_kappa_square_cubic_field_discriminant_not_square, ?_, ?_⟩
  · intro lam
    rfl
  · intro u
    rfl
  · intro u
    rfl
  · norm_num [killoLeyangCubicQuadraticSubfieldDiscriminant]
  · exact ⟨killo_leyang_kappa_square_cubic_field_mod5_irreducible_true,
      killo_leyang_kappa_square_cubic_field_discriminant_not_square⟩

end Omega.Folding
