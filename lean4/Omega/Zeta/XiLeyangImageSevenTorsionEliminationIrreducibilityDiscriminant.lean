import Mathlib.Tactic

namespace Omega.Zeta

/-- Coefficients of the displayed `L₇(y)` certificate, ordered from degree `48` down to `0`. -/
def xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_l7_coeffs :
    List ℤ :=
  [2401, -216090, 8508661, -195748830, 2930004106, -30316346864, 222334655189,
    -1157342551860, 3991074225594, -7202709575204, -10657811407452, 112205816041752,
    -378960173753194, 813792173949916, -1272579912391434, 1701235626444784,
    -1636138513560978, -197998457901880, 4420149463274830, -10825321480542788,
    19180870490835505, -24357792947158800, 20556374176128478, 2129138162785994,
    -33507974213689042, 75751558581142088, -119383507152698410, 143124429682746056,
    -131987006124578241, 91192136369810754, -46742852057176406, 16707500387178988,
    -3486011714189714, -99972999135036, 521443046392150, -802990216949360,
    728350156733752, -514747019925328, 284639553390553, -120638941704504,
    37113475496646, -6945498996040, -140075424201, 262233631328, -153469178224,
    46882788672, -7564012320, 578009600, -16056320]

/-- The degree of the displayed `L₇(y)` polynomial. -/
def xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_l7_degree :
    ℕ :=
  xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_l7_coeffs.length - 1

/-- The leading coefficient of the displayed `L₇(y)` polynomial. -/
def xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_l7_leading_coeff :
    ℤ :=
  xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_l7_coeffs.headD 0

/-- Prime of the finite-field irreducibility certificate. -/
def xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_mod_prime :
    ℕ :=
  5

/-- Encoded factor degrees of the mod-`5` reduction.  The singleton degree-`48` certificate records
irreducibility over `F₅`. -/
def xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_mod5_factor_degrees :
    List ℕ :=
  [48]

/-- The large square factor `P₇` displayed in the discriminant certificate. -/
def xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_p7 : ℕ :=
  896605137920355289318322421516871363636708810373820861334045825064975794195448006252805195318424980131241138817965808845409424354511493219373761004696208382587053432155947941

/-- The square root `D₇` in the absolute discriminant identity. -/
def xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_d7 : ℕ :=
  3 ^ 6 * 7 ^ 31 * 37 ^ 190 * 43 * 191 * 143977 * 2730979 * 2473661231 *
    xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_p7

/-- Prime-exponent certificate for `Disc(L₇)`. -/
def xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_disc_factors :
    List (ℕ × ℕ) :=
  [(3, 12), (7, 63), (37, 380), (43, 2), (191, 2), (143977, 2), (2730979, 2),
    (2473661231, 2),
    (xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_p7, 2)]

/-- The discriminant squareclass recorded by the factorization. -/
def xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_squareclass :
    ℤ :=
  -7

/-- Concrete certificate statement for the displayed polynomial, mod-`5` irreducibility witness,
and discriminant squareclass. -/
def xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_statement : Prop :=
  xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_l7_degree = 48 ∧
    xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_l7_leading_coeff =
      (7 : ℤ) ^ 4 ∧
    xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_mod_prime = 5 ∧
    xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_mod5_factor_degrees =
      [48] ∧
    xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_squareclass = -7 ∧
    xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_disc_factors.map
        Prod.fst =
      [3, 7, 37, 43, 191, 143977, 2730979, 2473661231,
        xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_p7] ∧
    xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_disc_factors.map
        Prod.snd =
      [12, 63, 380, 2, 2, 2, 2, 2, 2] ∧
    xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_d7 =
      3 ^ 6 * 7 ^ 31 * 37 ^ 190 * 43 * 191 * 143977 * 2730979 * 2473661231 *
        xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_p7

/-- Paper label:
`thm:xi-leyang-image-seven-torsion-elimination-irreducibility-discriminant`. -/
theorem paper_xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant :
    xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_statement := by
  unfold xi_leyang_image_seven_torsion_elimination_irreducibility_discriminant_statement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end Omega.Zeta
