import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.A4TNewmanOcticFieldArithmetic

namespace Omega.POM

/-- The requested paper signature for `prop:pom-a4t-newman-linear-response-constant` is false as
stated: at `zStar = 2`, the displayed rational formula defines `cStar`, but the claimed octic in
`cStar` does not vanish. This concrete witness justifies strengthening the Lean statement by
including the Newman-root hypothesis on `zStar`. -/
theorem pom_a4t_newman_linear_response_constant_counterexample :
    let zStar : ℝ := 2
    let cStar : ℝ := 4088 / 40205
    1 < zStar ∧
      cStar =
        (zStar ^ 3 * (3 * zStar ^ 8 + 3 * zStar ^ 7 - 6 * zStar ^ 4 - 7 * zStar ^ 3 +
            8 * zStar ^ 2 - 10)) /
          (2 * (zStar ^ 5 + zStar ^ 4 + 2 * zStar + 3) *
            (2 * zStar ^ 8 + 2 * zStar ^ 7 - 2 * zStar ^ 4 - 2 * zStar ^ 3 +
              4 * zStar ^ 2 - 5)) ∧
      591108823804 * cStar ^ 8 + 2774731980032 * cStar ^ 7 - 1469915176888 * cStar ^ 6 +
          2634492313776 * cStar ^ 5 + 1328731569804 * cStar ^ 4 + 269235674452 * cStar ^ 3 -
          5203293312 * cStar ^ 2 - 1491753550 * cStar - 268515639 ≠ 0 := by
  dsimp
  refine ⟨by norm_num, ?_, ?_⟩
  · norm_num
  · norm_num

/-- The Newman octic relation for the positive critical root `z_star`. -/
def pom_a4t_newman_linear_response_constant_newman_octic (zStar : ℝ) : Prop :=
  zStar ^ 8 - 2 * zStar ^ 6 - 2 * zStar ^ 5 - 2 * zStar ^ 4 - 2 * zStar ^ 3 - 2 = 0

/-- The displayed rational formula for the linear-response constant `c_star`. -/
noncomputable def pom_a4t_newman_linear_response_constant_formula (zStar : ℝ) : ℝ :=
  (zStar ^ 3 * (3 * zStar ^ 8 + 3 * zStar ^ 7 - 6 * zStar ^ 4 - 7 * zStar ^ 3 +
      8 * zStar ^ 2 - 10)) /
    (2 * (zStar ^ 5 + zStar ^ 4 + 2 * zStar + 3) *
      (2 * zStar ^ 8 + 2 * zStar ^ 7 - 2 * zStar ^ 4 - 2 * zStar ^ 3 + 4 * zStar ^ 2 - 5))

/-- The degree-`8` polynomial recorded for `c_star`. -/
def pom_a4t_newman_linear_response_constant_polynomial (cStar : ℝ) : ℝ :=
  591108823804 * cStar ^ 8 + 2774731980032 * cStar ^ 7 - 1469915176888 * cStar ^ 6 +
    2634492313776 * cStar ^ 5 + 1328731569804 * cStar ^ 4 + 269235674452 * cStar ^ 3 -
    5203293312 * cStar ^ 2 - 1491753550 * cStar - 268515639

/-- The denominator in the displayed rational formula. -/
def pom_a4t_newman_linear_response_constant_denominator (zStar : ℝ) : ℝ :=
  2 * (zStar ^ 5 + zStar ^ 4 + 2 * zStar + 3) *
    (2 * zStar ^ 8 + 2 * zStar ^ 7 - 2 * zStar ^ 4 - 2 * zStar ^ 3 + 4 * zStar ^ 2 - 5)

/-- The explicit quotient witnessing the elimination of `z_star` against the Newman octic. -/
def pom_a4t_newman_linear_response_constant_elimination_quotient (zStar : ℝ) : ℝ :=
  -17597440917504 * zStar ^ 96 - 281559054680064 * zStar ^ 95 -
    2220210462425088 * zStar ^ 94 - 11552719962341376 * zStar ^ 93 -
    45097550519304192 * zStar ^ 92 - 143450261671084032 * zStar ^ 91 -
    388974505377435648 * zStar ^ 90 - 903024585837793280 * zStar ^ 89 -
    1752119033135084544 * zStar ^ 88 - 2728185829224878080 * zStar ^ 87 -
    3171602356464004096 * zStar ^ 86 - 2169022039170837504 * zStar ^ 85 +
    864691958736646272 * zStar ^ 84 + 6020750023126147328 * zStar ^ 83 +
    14256392976671184768 * zStar ^ 82 + 29289256540147629824 * zStar ^ 81 +
    55326463827343747708 * zStar ^ 80 + 88989141196364583904 * zStar ^ 79 +
    114737201364913895816 * zStar ^ 78 + 113847041263125330648 * zStar ^ 77 +
    82493717991416956784 * zStar ^ 76 + 33121106679554678648 * zStar ^ 75 -
    47475204245679277424 * zStar ^ 74 - 223435870795400112560 * zStar ^ 73 -
    520788674971087426508 * zStar ^ 72 - 829999983413365083920 * zStar ^ 71 -
    983819594341787998952 * zStar ^ 70 - 972353109228867514952 * zStar ^ 69 -
    1071092745590285339096 * zStar ^ 68 - 1386867567915039097640 * zStar ^ 67 -
    1071541697782579757152 * zStar ^ 66 + 890065319250716399488 * zStar ^ 65 +
    3571686832373587809032 * zStar ^ 64 + 4382378439390229242912 * zStar ^ 63 +
    2276710718873500748016 * zStar ^ 62 + 672306836293596819936 * zStar ^ 61 +
    5552440781022687790120 * zStar ^ 60 + 14843496840945497138624 * zStar ^ 59 +
    13421335868042461878176 * zStar ^ 58 - 6188375180036164911792 * zStar ^ 57 -
    24324079538476007327032 * zStar ^ 56 - 15127656728130254630512 * zStar ^ 55 +
    16738619225645893748592 * zStar ^ 54 + 26852451683324437266672 * zStar ^ 53 -
    25628938817468127627552 * zStar ^ 52 - 92647405280159909337744 * zStar ^ 51 -
    59358449338330615898576 * zStar ^ 50 + 66072139486660143910944 * zStar ^ 49 +
    113791105570333092529792 * zStar ^ 48 - 3674225494320348524256 * zStar ^ 47 -
    154779123662211985136864 * zStar ^ 46 - 116262933228398933775520 * zStar ^ 45 +
    164098004552638527231776 * zStar ^ 44 + 333259752973244092239776 * zStar ^ 43 +
    30770961452964685634976 * zStar ^ 42 - 365742298951478596152256 * zStar ^ 41 -
    209518677857769893972996 * zStar ^ 40 + 304280748342057356740736 * zStar ^ 39 +
    454572836589352580710840 * zStar ^ 38 - 3674595577933116569800 * zStar ^ 37 -
    599699122969600352625112 * zStar ^ 36 - 459285205568195940992488 * zStar ^ 35 +
    484832550016558642372144 * zStar ^ 34 + 770290215920804747675488 * zStar ^ 33 -
    285915515100982840078648 * zStar ^ 32 - 955656632125067306133472 * zStar ^ 31 -
    128675453101258266392240 * zStar ^ 30 + 749129022241531417739488 * zStar ^ 29 +
    508404678842467630719520 * zStar ^ 28 - 310160876399756553746848 * zStar ^ 27 -
    801073682384666439535552 * zStar ^ 26 - 154410315274338314999392 * zStar ^ 25 +
    1007318760380942808494544 * zStar ^ 24 + 525804682155108843088640 * zStar ^ 23 -
    977825534825380505136960 * zStar ^ 22 - 577907305423416367310816 * zStar ^ 21 +
    830204388023923675513760 * zStar ^ 20 + 462249437054625836184608 * zStar ^ 19 -
    551261155929360376369024 * zStar ^ 18 - 267122075508805657579904 * zStar ^ 17 +
    272072634270843769099552 * zStar ^ 16 + 106389221465288383409280 * zStar ^ 15 -
    90157843899361927102720 * zStar ^ 14 - 34049366622560606486400 * zStar ^ 13 -
    6569977253040778441600 * zStar ^ 12 - 3403021434124628112000 * zStar ^ 11 +
    21546142004467027984000 * zStar ^ 10 + 6918790866415022400000 * zStar ^ 9 -
    17214072047550667800000 * zStar ^ 8 - 6773898235158079200000 * zStar ^ 7 +
    7585140433280331600000 * zStar ^ 6 + 3866079040790274000000 * zStar ^ 5 -
    1995628099205286000000 * zStar ^ 4 - 1188189758044170000000 * zStar ^ 3 +
    532434290260320000000 * zStar ^ 2 + 469794961994400000000 * zStar +
    88086555373950000000

/-- Paper-facing strengthened statement: once the omitted Newman-root hypothesis is included, the
displayed rational formula for `c_star` satisfies the recorded degree-`8` polynomial and packages
the previously verified Newman octic arithmetic data. -/
def pom_a4t_newman_linear_response_constant_statement : Prop :=
  ∀ {zStar : ℝ},
    1 < zStar →
    pom_a4t_newman_linear_response_constant_newman_octic zStar →
    let cStar := pom_a4t_newman_linear_response_constant_formula zStar
    pom_a4t_newman_linear_response_constant_polynomial cStar = 0 ∧
      (a4tNewmanOcticEisensteinAtTwo ∧
        a4tNewmanOcticDiscriminant = -(2 ^ 10 * 7 ^ 2 * 23 ^ 2 * 1151 : ℤ) ∧
        a4tNewmanOcticSignature = (2, 3) ∧
        a4tNewmanOcticUnitRank = 4) ∧
      pom_a4t_newman_octic_field_tame_package ∧
      pom_a4t_newman_octic_field_prime_decomp_package

lemma pom_a4t_newman_linear_response_constant_formula_denominator_ne
    {zStar : ℝ} (hz1 : 1 < zStar)
    (hz :
      pom_a4t_newman_linear_response_constant_newman_octic zStar) :
    pom_a4t_newman_linear_response_constant_denominator zStar ≠ 0 := by
  have hz_pos : 0 < zStar := lt_trans zero_lt_one hz1
  have hfirst_pos : 0 < zStar ^ 5 + zStar ^ 4 + 2 * zStar + 3 := by
    positivity
  have hz_pow_gap : 0 < zStar ^ 7 - 1 := by
    have hz_sub_pos : 0 < zStar - 1 := sub_pos.mpr hz1
    have hfactor :
        zStar ^ 7 - 1 =
          (zStar - 1) *
            (zStar ^ 6 + zStar ^ 5 + zStar ^ 4 + zStar ^ 3 + zStar ^ 2 + zStar + 1) := by
      ring
    rw [hfactor]
    positivity
  have hz7_gt : 1 < zStar ^ 7 := by
    linarith
  have hz_rewrite :
      zStar ^ 8 = 2 * zStar ^ 6 + 2 * zStar ^ 5 + 2 * zStar ^ 4 + 2 * zStar ^ 3 + 2 := by
    dsimp [pom_a4t_newman_linear_response_constant_newman_octic] at hz
    linarith
  have hsecond_pos :
      0 <
        2 * zStar ^ 8 + 2 * zStar ^ 7 - 2 * zStar ^ 4 - 2 * zStar ^ 3 + 4 * zStar ^ 2 - 5 := by
    rw [hz_rewrite]
    nlinarith
  have hden_pos : 0 < pom_a4t_newman_linear_response_constant_denominator zStar := by
    dsimp [pom_a4t_newman_linear_response_constant_denominator]
    positivity
  linarith

set_option maxHeartbeats 0 in
lemma pom_a4t_newman_linear_response_constant_elimination_identity
    (zStar : ℝ)
    (hden_ne : pom_a4t_newman_linear_response_constant_denominator zStar ≠ 0) :
    pom_a4t_newman_linear_response_constant_polynomial
        (pom_a4t_newman_linear_response_constant_formula zStar) *
        pom_a4t_newman_linear_response_constant_denominator zStar ^ 8 =
      (zStar ^ 8 - 2 * zStar ^ 6 - 2 * zStar ^ 5 - 2 * zStar ^ 4 - 2 * zStar ^ 3 - 2) *
        pom_a4t_newman_linear_response_constant_elimination_quotient zStar := by
  have hfirst_ne : zStar ^ 5 + zStar ^ 4 + 2 * zStar + 3 ≠ 0 := by
    intro hfirst
    apply hden_ne
    simp [pom_a4t_newman_linear_response_constant_denominator, hfirst]
  have hsecond_ne :
      2 * zStar ^ 8 + 2 * zStar ^ 7 - 2 * zStar ^ 4 - 2 * zStar ^ 3 +
          4 * zStar ^ 2 - 5 ≠ 0 := by
    intro hsecond
    apply hden_ne
    simp [pom_a4t_newman_linear_response_constant_denominator, hsecond]
  have hfirst_nf_ne : zStar * (zStar ^ 3 * (zStar + 1) + 2) + 3 ≠ 0 := by
    convert hfirst_ne using 1 <;> ring
  have hsecond_nf_ne :
      zStar ^ 2 * (zStar * 2 * (zStar * (zStar ^ 3 * (zStar + 1) - 1) - 1) + 4) -
          5 ≠ 0 := by
    convert hsecond_ne using 1 <;> ring
  unfold pom_a4t_newman_linear_response_constant_polynomial
    pom_a4t_newman_linear_response_constant_formula
    pom_a4t_newman_linear_response_constant_elimination_quotient
  field_simp [pom_a4t_newman_linear_response_constant_denominator, hfirst_ne, hsecond_ne,
    hfirst_nf_ne, hsecond_nf_ne]
  unfold pom_a4t_newman_linear_response_constant_denominator
  set_option maxRecDepth 10000 in
    ring1

lemma pom_a4t_newman_linear_response_constant_polynomial_eq_zero
    {zStar : ℝ} (hz1 : 1 < zStar)
    (hz :
      pom_a4t_newman_linear_response_constant_newman_octic zStar) :
    pom_a4t_newman_linear_response_constant_polynomial
        (pom_a4t_newman_linear_response_constant_formula zStar) = 0 := by
  have hden_ne :
      pom_a4t_newman_linear_response_constant_denominator zStar ≠ 0 :=
    pom_a4t_newman_linear_response_constant_formula_denominator_ne hz1 hz
  have hmul :
      pom_a4t_newman_linear_response_constant_polynomial
          (pom_a4t_newman_linear_response_constant_formula zStar) *
          pom_a4t_newman_linear_response_constant_denominator zStar ^ 8 =
        0 := by
    rw [pom_a4t_newman_linear_response_constant_elimination_identity zStar hden_ne]
    dsimp [pom_a4t_newman_linear_response_constant_newman_octic] at hz
    simp [hz]
  exact (mul_eq_zero.mp hmul).resolve_right (pow_ne_zero 8 hden_ne)

theorem paper_pom_a4t_newman_linear_response_constant :
    pom_a4t_newman_linear_response_constant_statement := by
  intro zStar hz1 hz
  refine ⟨pom_a4t_newman_linear_response_constant_polynomial_eq_zero hz1 hz, ?_, ?_, ?_⟩
  · exact paper_pom_a4t_newman_octic_field_basic
  · exact paper_pom_a4t_newman_octic_field_tame
  · exact paper_pom_a4t_newman_octic_field_prime_decomp

end Omega.POM
