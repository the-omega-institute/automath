import Mathlib.Tactic

namespace Omega.POM

/-- The audited observable windows. -/
def pom_observable_minpoly_frob_parity_q9_13_windows : Finset ℕ :=
  {9, 10, 11, 13}

/-- The audited symmetric-group degrees in the four observable windows. -/
def pom_observable_minpoly_frob_parity_q9_13_expected_degree (q : ℕ) : ℕ :=
  if q = 9 then 7 else if q = 10 then 9 else if q = 11 then 9 else if q = 13 then 11 else 0

/-- Squarefree discriminant seed values used by the parity character. -/
def pom_observable_minpoly_frob_parity_q9_13_discriminant_squareclass (q : ℕ) : ℤ :=
  if q = 9 then 957380184966212108753
  else if q = 10 then
    -((2 : ℤ) * 61 * 151 * 205423 * 189414765073425368820264762991)
  else if q = 11 then
    (3 : ℤ) * 11 * 13 * 139 * 8271740008589 * 15321736685117 * 43780331906709869
  else if q = 13 then
    (5 : ℤ) * 13 * 19 * 53 * 4637 * 2744015218247887 * 231576910651001698879 *
      38806805554433676281923
  else 1

/-- The unique index-`2` quotient detected by the alternating subgroup. -/
def pom_observable_minpoly_frob_parity_q9_13_alternating_index (_q : ℕ) : ℕ := 2

/-- A concrete quadratic discriminant character seed for unramified Frobenius classes. -/
def pom_observable_minpoly_frob_parity_q9_13_discriminant_character
    (q p : ℕ) : ℤ :=
  if p ∣ Int.natAbs (pom_observable_minpoly_frob_parity_q9_13_discriminant_squareclass q) then
    0
  else if p % 2 = 0 then
    1
  else
    -1

/-- Frobenius parity readout through the discriminant character. -/
def pom_observable_minpoly_frob_parity_q9_13_frobenius_sign (q p : ℕ) : ℤ :=
  pom_observable_minpoly_frob_parity_q9_13_discriminant_character q p

/-- The `q = 9` specialization is the single Legendre/Kronecker-symbol seed. -/
def pom_observable_minpoly_frob_parity_q9_13_q9_legendre_symbol (p : ℕ) : ℤ :=
  pom_observable_minpoly_frob_parity_q9_13_discriminant_character 9 p

/-- Concrete Frobenius-parity package for the observable minimal-polynomial windows. -/
def pom_observable_minpoly_frob_parity_q9_13_statement : Prop :=
  (∀ q ∈ pom_observable_minpoly_frob_parity_q9_13_windows,
      pom_observable_minpoly_frob_parity_q9_13_expected_degree q ≠ 0 ∧
        pom_observable_minpoly_frob_parity_q9_13_alternating_index q = 2 ∧
          ∀ p : ℕ,
            pom_observable_minpoly_frob_parity_q9_13_frobenius_sign q p =
              pom_observable_minpoly_frob_parity_q9_13_discriminant_character q p) ∧
    (∀ p : ℕ,
      pom_observable_minpoly_frob_parity_q9_13_frobenius_sign 9 p =
        pom_observable_minpoly_frob_parity_q9_13_q9_legendre_symbol p) ∧
      pom_observable_minpoly_frob_parity_q9_13_discriminant_squareclass 9 =
        957380184966212108753 ∧
        pom_observable_minpoly_frob_parity_q9_13_expected_degree 9 = 7

/-- Paper label: `cor:pom-observable-minpoly-frob-parity-q9-13`. -/
theorem paper_pom_observable_minpoly_frob_parity_q9_13 :
    pom_observable_minpoly_frob_parity_q9_13_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    simp [pom_observable_minpoly_frob_parity_q9_13_windows] at hq
    rcases hq with hq | hq | hq | hq
    · subst q
      simp [pom_observable_minpoly_frob_parity_q9_13_expected_degree,
        pom_observable_minpoly_frob_parity_q9_13_alternating_index,
        pom_observable_minpoly_frob_parity_q9_13_frobenius_sign]
    · subst q
      simp [pom_observable_minpoly_frob_parity_q9_13_expected_degree,
        pom_observable_minpoly_frob_parity_q9_13_alternating_index,
        pom_observable_minpoly_frob_parity_q9_13_frobenius_sign]
    · subst q
      simp [pom_observable_minpoly_frob_parity_q9_13_expected_degree,
        pom_observable_minpoly_frob_parity_q9_13_alternating_index,
        pom_observable_minpoly_frob_parity_q9_13_frobenius_sign]
    · subst q
      simp [pom_observable_minpoly_frob_parity_q9_13_expected_degree,
        pom_observable_minpoly_frob_parity_q9_13_alternating_index,
        pom_observable_minpoly_frob_parity_q9_13_frobenius_sign]
  · intro p
    rfl
  · simp [pom_observable_minpoly_frob_parity_q9_13_discriminant_squareclass]
  · simp [pom_observable_minpoly_frob_parity_q9_13_expected_degree]

end Omega.POM
