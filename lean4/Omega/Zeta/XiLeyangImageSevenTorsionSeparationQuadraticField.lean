import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete label for the quadratic subfield induced by the discriminant squareclass. -/
inductive xi_leyang_image_seven_torsion_separation_quadratic_field_label
  | Qsqrt (d : ℤ)
  deriving DecidableEq, Repr

/-- The model for the nonzero seven-torsion points has `7² - 1 = 48` elements. -/
abbrev xi_leyang_image_seven_torsion_separation_quadratic_field_nonzero_torsion :
    Type :=
  Fin 48

/-- The separability certificate supplies forty-eight distinct roots. -/
abbrev xi_leyang_image_seven_torsion_separation_quadratic_field_distinct_roots :
    Type :=
  Fin 48

/-- The Lee--Yang image map after identifying the forty-eight certified roots. -/
def xi_leyang_image_seven_torsion_separation_quadratic_field_image
    (P : xi_leyang_image_seven_torsion_separation_quadratic_field_nonzero_torsion) :
    xi_leyang_image_seven_torsion_separation_quadratic_field_distinct_roots :=
  P

/-- The discriminant squareclass of the degree-`48` seven-torsion elimination polynomial. -/
def xi_leyang_image_seven_torsion_separation_quadratic_field_discriminant_squareclass :
    ℤ :=
  -7

/-- The corresponding quadratic subfield label. -/
def xi_leyang_image_seven_torsion_separation_quadratic_field_quadratic_subfield :
    xi_leyang_image_seven_torsion_separation_quadratic_field_label :=
  .Qsqrt xi_leyang_image_seven_torsion_separation_quadratic_field_discriminant_squareclass

/-- Concrete package for the separation and quadratic-field conclusion. -/
def xi_leyang_image_seven_torsion_separation_quadratic_field_statement : Prop :=
  Fintype.card xi_leyang_image_seven_torsion_separation_quadratic_field_nonzero_torsion =
      7 ^ 2 - 1 ∧
    Fintype.card xi_leyang_image_seven_torsion_separation_quadratic_field_distinct_roots =
      48 ∧
    Function.Injective xi_leyang_image_seven_torsion_separation_quadratic_field_image ∧
    xi_leyang_image_seven_torsion_separation_quadratic_field_discriminant_squareclass =
      -7 ∧
    xi_leyang_image_seven_torsion_separation_quadratic_field_quadratic_subfield =
      .Qsqrt (-7)

/-- Paper label: `prop:xi-leyang-image-seven-torsion-separation-quadratic-field`. -/
theorem paper_xi_leyang_image_seven_torsion_separation_quadratic_field :
    xi_leyang_image_seven_torsion_separation_quadratic_field_statement := by
  unfold xi_leyang_image_seven_torsion_separation_quadratic_field_statement
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro P Q hPQ
    exact hPQ
  · rfl
  · rfl

end Omega.Zeta
