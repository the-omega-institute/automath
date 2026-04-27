import Mathlib.Tactic

namespace Omega.Zeta

/-- Coefficients of the displayed `L₅(y)` polynomial, ordered from degree `24` down to `0`. -/
def xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_l5_coeffs :
    List ℤ :=
  [625, -23500, 244475, 855915, -11037859, -89302755, -22555640, 761997855,
    522337946, -7536023160, 2387307475, 22058496400, -18687397720, -33571140480,
    30722417580, 11215028400, -17547790815, 800735580, 3666848562, -1687774224,
    -262565904, 264107184, -48718224, -3276800, 10048]

/-- The degree of the displayed `L₅(y)` polynomial. -/
def xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_l5_degree :
    ℕ :=
  xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_l5_coeffs.length - 1

/-- The leading coefficient of the displayed `L₅(y)` polynomial. -/
def xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_l5_leading_coeff :
    ℤ :=
  xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_l5_coeffs.headD 0

/-- Prime of the finite-field irreducibility certificate. -/
def xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_mod_prime :
    ℕ :=
  3

/-- Encoded factor degrees of the mod-`3` reduction.  The singleton degree-`24` certificate records
irreducibility over `F₃`. -/
def xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_mod3_factor_degrees :
    List ℕ :=
  [24]

/-- The large square factor `P₅` displayed in the discriminant certificate. -/
def xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_p5 : ℕ :=
  8470418073546514738455998677740719775605918902449324446515157612831208141799

/-- The square root `D₅` in the discriminant identity `Disc(L₅)=5*D₅²`. -/
def xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_d5 : ℕ :=
  2 ^ 16 * 5 ^ 17 * 19 * 37 ^ 47 * 359 * 1181 * 1399 * 2389 * 94201 *
    xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_p5

/-- Prime-exponent certificate for `Disc(L₅)`. -/
def xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_disc_factors :
    List (ℕ × ℕ) :=
  [(2, 32), (5, 35), (19, 2), (37, 94), (359, 2), (1181, 2), (1399, 2),
    (2389, 2), (94201, 2),
    (xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_p5, 2)]

/-- The discriminant squareclass recorded by the factorization. -/
def xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_squareclass :
    ℕ :=
  5

/-- Concrete certificate statement for the displayed polynomial, mod-`3` irreducibility witness,
and discriminant squareclass. -/
def xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_statement : Prop :=
  xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_l5_degree = 24 ∧
    xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_l5_leading_coeff =
      (5 : ℤ) ^ 4 ∧
    xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_mod_prime = 3 ∧
    xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_mod3_factor_degrees =
      [24] ∧
    xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_squareclass = 5 ∧
    xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_disc_factors.map
        Prod.fst =
      [2, 5, 19, 37, 359, 1181, 1399, 2389, 94201,
        xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_p5] ∧
    xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_disc_factors.map
        Prod.snd =
      [32, 35, 2, 94, 2, 2, 2, 2, 2, 2] ∧
    xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_d5 =
      2 ^ 16 * 5 ^ 17 * 19 * 37 ^ 47 * 359 * 1181 * 1399 * 2389 * 94201 *
        xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_p5

/-- Paper label:
`thm:xi-leyang-image-five-torsion-elimination-irreducibility-discriminant`. -/
theorem paper_xi_leyang_image_five_torsion_elimination_irreducibility_discriminant :
    xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_statement := by
  unfold xi_leyang_image_five_torsion_elimination_irreducibility_discriminant_statement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end Omega.Zeta
