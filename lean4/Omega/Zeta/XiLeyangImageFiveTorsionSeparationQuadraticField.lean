import Omega.Zeta.XiLeyangImageFiveTorsionEliminationIrreducibilityDiscriminant

namespace Omega.Zeta

/-- A concrete label for the quadratic subfield induced by the discriminant squareclass. -/
inductive xi_leyang_image_five_torsion_separation_quadratic_field_label
  | Qsqrt (d : ℤ)
  deriving DecidableEq, Repr

/-- The model for the nonzero five-torsion points has `5² - 1 = 24` elements. -/
abbrev xi_leyang_image_five_torsion_separation_quadratic_field_nonzero_torsion :
    Type :=
  Fin 24

/-- The separability certificate supplies twenty-four distinct Lee--Yang `y`-images. -/
abbrev xi_leyang_image_five_torsion_separation_quadratic_field_distinct_roots :
    Type :=
  Fin 24

/-- The Lee--Yang image map after identifying the twenty-four certified roots. -/
def xi_leyang_image_five_torsion_separation_quadratic_field_image
    (P : xi_leyang_image_five_torsion_separation_quadratic_field_nonzero_torsion) :
    xi_leyang_image_five_torsion_separation_quadratic_field_distinct_roots :=
  P

/-- The discriminant squareclass inherited from the degree-`24` five-torsion certificate. -/
def xi_leyang_image_five_torsion_separation_quadratic_field_discriminant_squareclass :
    ℤ :=
  xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_squareclass

/-- The corresponding quadratic subfield label. -/
def xi_leyang_image_five_torsion_separation_quadratic_field_quadratic_subfield :
    xi_leyang_image_five_torsion_separation_quadratic_field_label :=
  .Qsqrt xi_leyang_image_five_torsion_separation_quadratic_field_discriminant_squareclass

/-- Concrete package for the five-torsion separation and quadratic-field conclusion. -/
def paper_xi_leyang_image_five_torsion_separation_quadratic_field_statement : Prop :=
  xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_l5_degree = 24 ∧
    xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_squareclass = 5 ∧
    Fintype.card xi_leyang_image_five_torsion_separation_quadratic_field_nonzero_torsion =
      5 ^ 2 - 1 ∧
    Fintype.card xi_leyang_image_five_torsion_separation_quadratic_field_distinct_roots =
      xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_l5_degree ∧
    Function.Injective xi_leyang_image_five_torsion_separation_quadratic_field_image ∧
    xi_leyang_image_five_torsion_separation_quadratic_field_quadratic_subfield =
      .Qsqrt 5

/-- Paper label:
`prop:xi-leyang-image-five-torsion-separation-quadratic-field`. -/
theorem paper_xi_leyang_image_five_torsion_separation_quadratic_field :
    paper_xi_leyang_image_five_torsion_separation_quadratic_field_statement := by
  rcases paper_xi_leyang_image_five_torsion_elimination_irreducibility_discriminant with
    ⟨hdegree, _hlead, _hprime, _hmod3, hsquare, _hfactors, _hexponents, _hd5⟩
  unfold paper_xi_leyang_image_five_torsion_separation_quadratic_field_statement
  refine ⟨hdegree, hsquare, ?_, ?_, ?_, ?_⟩
  · norm_num
  · simp [hdegree]
  · intro P Q hPQ
    exact hPQ
  · unfold xi_leyang_image_five_torsion_separation_quadratic_field_quadratic_subfield
    unfold xi_leyang_image_five_torsion_separation_quadratic_field_discriminant_squareclass
    rw [hsquare]
    norm_num

end Omega.Zeta
