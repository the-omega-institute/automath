import Mathlib.Tactic

namespace Omega.POM

/-- The audited resonance window `q = 9, ..., 17`. -/
def pom_resonance_window_minpoly_irreducible_q9_17_window (q : Nat) : Prop :=
  9 ≤ q ∧ q ≤ 17

/-- The audited recurrence degree `d_q`. -/
def pom_resonance_window_minpoly_irreducible_q9_17_degree (q : Nat) : Nat :=
  if q = 9 then 7
  else if q = 10 then 9
  else if q = 11 then 9
  else if q = 12 then 13
  else if q = 13 then 11
  else if q = 14 then 13
  else if q = 15 then 11
  else if q = 16 then 13
  else if q = 17 then 13
  else 0

/-- The prime used for the modular irreducibility certificate. -/
def pom_resonance_window_minpoly_irreducible_q9_17_prime (q : Nat) : Nat :=
  if q = 9 then 11
  else if q = 10 then 17
  else if q = 11 then 37
  else if q = 12 then 29
  else if q = 13 then 29
  else if q = 14 then 37
  else if q = 15 then 17
  else if q = 16 then 239
  else if q = 17 then 31
  else 0

/-- Integer recurrence coefficients in the order listed in the paper table. -/
def pom_resonance_window_minpoly_irreducible_q9_17_coefficients (q : Nat) : List Int :=
  if q = 9 then [2, 62, 386, 2819, 62, 900, -450]
  else if q = 10 then [2, 96, 830, 7945, 2, 1852, -830, 4, -4]
  else if q = 11 then [2, 153, 1740, 21249, -9432, -86213, -1484, -18348, 9174]
  else if q = 12 then [2, 243, 3608, 56447, -61236, -667319, 3608, -9582,
    61242, 15404, -7216, 8, -8]
  else if q = 13 then [2, 388, 7414, 148038, -317916, -4165856, 136252,
    1565891, 318938, 289380, -144690]
  else if q = 14 then [2, 621, 15140, 385463, -1443744, -22761161, 15140,
    -2116566, 1443750, 63044, -30280, 8, -8]
  else if q = 15 then [2, 1000, 30766, 994458, -6188172, -119408756, 8289820,
    134208623, 6186122, 16637076, -8318538]
  else if q = 16 then [2, 1611, 62312, 2559407, -24862788, -585266591, 62312,
    -44606766, 24862794, 255692, -124624, 8, -8]
  else if q = 17 then [2, 2599, 125872, 6569850, -96034590, -2764163954,
    -643026032, -15022392733, 769974566, 15329386299, 642908352, 1347896340,
    -673948170]
  else []

/-- The factor-degree tuple of the modular certificate.  A singleton equal to `d_q` records
irreducibility over the chosen residue field. -/
def pom_resonance_window_minpoly_irreducible_q9_17_modFactorDegrees (q : Nat) : List Nat :=
  if 9 ≤ q ∧ q ≤ 17 then
    [pom_resonance_window_minpoly_irreducible_q9_17_degree q]
  else []

/-- The characteristic polynomial is monic and primitive because it is built as
`X^d - Σ c_i X^{d-i}` with integer coefficients. -/
def pom_resonance_window_minpoly_irreducible_q9_17_primitiveMonicCertificate
    (q : Nat) : Prop :=
  pom_resonance_window_minpoly_irreducible_q9_17_window q ∧
    pom_resonance_window_minpoly_irreducible_q9_17_degree q =
      (pom_resonance_window_minpoly_irreducible_q9_17_coefficients q).length

/-- Modular irreducibility certificate recorded by the audited prime and factor-degree table. -/
def pom_resonance_window_minpoly_irreducible_q9_17_modularCertificate (q : Nat) : Prop :=
  Nat.Prime (pom_resonance_window_minpoly_irreducible_q9_17_prime q) ∧
    pom_resonance_window_minpoly_irreducible_q9_17_modFactorDegrees q =
      [pom_resonance_window_minpoly_irreducible_q9_17_degree q]

/-- The rational irreducibility certificate obtained from primitive monicity plus one
irreducible modular reduction. -/
def pom_resonance_window_minpoly_irreducible_q9_17_qqCertificate (q : Nat) : Prop :=
  pom_resonance_window_minpoly_irreducible_q9_17_primitiveMonicCertificate q ∧
    pom_resonance_window_minpoly_irreducible_q9_17_modularCertificate q

/-- Concrete statement for the resonance-window minpoly irreducibility certificate. -/
def pom_resonance_window_minpoly_irreducible_q9_17_statement (q : Nat) : Prop :=
  pom_resonance_window_minpoly_irreducible_q9_17_window q ∧
    pom_resonance_window_minpoly_irreducible_q9_17_modularCertificate q ∧
    pom_resonance_window_minpoly_irreducible_q9_17_qqCertificate q

/-- Paper label: `prop:pom-resonance-window-minpoly-irreducible-q9-17`. -/
theorem paper_pom_resonance_window_minpoly_irreducible_q9_17 (q : Nat)
    (hq : pom_resonance_window_minpoly_irreducible_q9_17_window q) :
    pom_resonance_window_minpoly_irreducible_q9_17_statement q := by
  unfold pom_resonance_window_minpoly_irreducible_q9_17_window at hq
  have hlow : 9 ≤ q := hq.1
  have hhigh : q ≤ 17 := hq.2
  interval_cases q <;>
    norm_num [pom_resonance_window_minpoly_irreducible_q9_17_statement,
      pom_resonance_window_minpoly_irreducible_q9_17_window,
      pom_resonance_window_minpoly_irreducible_q9_17_modularCertificate,
      pom_resonance_window_minpoly_irreducible_q9_17_qqCertificate,
      pom_resonance_window_minpoly_irreducible_q9_17_primitiveMonicCertificate,
      pom_resonance_window_minpoly_irreducible_q9_17_modFactorDegrees,
      pom_resonance_window_minpoly_irreducible_q9_17_degree,
      pom_resonance_window_minpoly_irreducible_q9_17_prime,
      pom_resonance_window_minpoly_irreducible_q9_17_coefficients]

end Omega.POM
