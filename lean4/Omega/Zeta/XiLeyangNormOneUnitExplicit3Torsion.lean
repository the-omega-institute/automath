import Mathlib.Tactic
import Omega.Zeta.XiLeyangCardanoNumeratorDivisorVisibility

namespace Omega.Zeta

/-- Concrete divisor carrier for the Lee--Yang certificate.  The three coordinates record the
formal coefficients of `Qminus`, `Qplus`, and `infinity`. -/
abbrev xi_leyang_norm_one_unit_explicit_3torsion_divisor := Fin 3 → ℤ

/-- Concrete data for the Lee--Yang norm-one unit and its induced divisor-class certificate. -/
structure xi_leyang_norm_one_unit_explicit_3torsion_data where
  xi_leyang_norm_one_unit_explicit_3torsion_s : ℚ
  xi_leyang_norm_one_unit_explicit_3torsion_y : ℚ
  xi_leyang_norm_one_unit_explicit_3torsion_u : ℚ
  xi_leyang_norm_one_unit_explicit_3torsion_Qminus :
    xi_leyang_norm_one_unit_explicit_3torsion_divisor
  xi_leyang_norm_one_unit_explicit_3torsion_Qplus :
    xi_leyang_norm_one_unit_explicit_3torsion_divisor
  xi_leyang_norm_one_unit_explicit_3torsion_infinity :
    xi_leyang_norm_one_unit_explicit_3torsion_divisor
  div : ℚ → xi_leyang_norm_one_unit_explicit_3torsion_divisor
  classMap : xi_leyang_norm_one_unit_explicit_3torsion_divisor →+ ZMod 3
  xi_leyang_norm_one_unit_explicit_3torsion_s_sq :
    xi_leyang_norm_one_unit_explicit_3torsion_s ^ 2 = -3
  xi_leyang_norm_one_unit_explicit_3torsion_curve_eq :
    xi_leyang_norm_one_unit_explicit_3torsion_u ^ 2 =
      -xi_leyang_norm_one_unit_explicit_3torsion_y *
        (xi_leyang_norm_one_unit_explicit_3torsion_y - 1) *
          (256 * xi_leyang_norm_one_unit_explicit_3torsion_y ^ 3 +
            411 * xi_leyang_norm_one_unit_explicit_3torsion_y ^ 2 +
              165 * xi_leyang_norm_one_unit_explicit_3torsion_y + 32)
  xi_leyang_norm_one_unit_explicit_3torsion_denom_ne_zero :
    16 * (2 * xi_leyang_norm_one_unit_explicit_3torsion_y + 1) ^ 3 ≠ 0
  xi_leyang_norm_one_unit_explicit_3torsion_div_mul :
    ∀ a b : ℚ, div (a * b) = div a + div b
  xi_leyang_norm_one_unit_explicit_3torsion_div_div :
    ∀ a b : ℚ, div (a / b) = div a - div b
  xi_leyang_norm_one_unit_explicit_3torsion_div_pow :
    ∀ (a : ℚ) (n : ℕ), div (a ^ n) = n • div a
  xi_leyang_norm_one_unit_explicit_3torsion_div_sixteen :
    div 16 = 0
  xi_leyang_norm_one_unit_explicit_3torsion_div_A_minus :
    div (128 * xi_leyang_norm_one_unit_explicit_3torsion_y ^ 3 +
        219 * xi_leyang_norm_one_unit_explicit_3torsion_y ^ 2 +
          69 * xi_leyang_norm_one_unit_explicit_3torsion_y + 16 -
            3 * xi_leyang_norm_one_unit_explicit_3torsion_s *
              xi_leyang_norm_one_unit_explicit_3torsion_u) =
      (6 : ℕ) • xi_leyang_norm_one_unit_explicit_3torsion_Qminus -
        (6 : ℕ) • xi_leyang_norm_one_unit_explicit_3torsion_infinity
  xi_leyang_norm_one_unit_explicit_3torsion_div_two_y_plus_one :
    div (2 * xi_leyang_norm_one_unit_explicit_3torsion_y + 1) =
      xi_leyang_norm_one_unit_explicit_3torsion_Qminus +
          xi_leyang_norm_one_unit_explicit_3torsion_Qplus -
        (2 : ℕ) • xi_leyang_norm_one_unit_explicit_3torsion_infinity
  xi_leyang_norm_one_unit_explicit_3torsion_principal_eta :
    classMap (div ((128 * xi_leyang_norm_one_unit_explicit_3torsion_y ^ 3 +
        219 * xi_leyang_norm_one_unit_explicit_3torsion_y ^ 2 +
          69 * xi_leyang_norm_one_unit_explicit_3torsion_y + 16 -
            3 * xi_leyang_norm_one_unit_explicit_3torsion_s *
              xi_leyang_norm_one_unit_explicit_3torsion_u) /
      (16 * (2 * xi_leyang_norm_one_unit_explicit_3torsion_y + 1) ^ 3))) = 0
  xi_leyang_norm_one_unit_explicit_3torsion_genus_obstruction :
    classMap (xi_leyang_norm_one_unit_explicit_3torsion_Qminus -
      xi_leyang_norm_one_unit_explicit_3torsion_Qplus) ≠ 0

namespace xi_leyang_norm_one_unit_explicit_3torsion_data

/-- The Cardano numerator polynomial `A(y)`. -/
def xi_leyang_norm_one_unit_explicit_3torsion_A
    (D : xi_leyang_norm_one_unit_explicit_3torsion_data) : ℚ :=
  128 * D.xi_leyang_norm_one_unit_explicit_3torsion_y ^ 3 +
    219 * D.xi_leyang_norm_one_unit_explicit_3torsion_y ^ 2 +
      69 * D.xi_leyang_norm_one_unit_explicit_3torsion_y + 16

/-- The displayed norm-one unit. -/
def xi_leyang_norm_one_unit_explicit_3torsion_eta
    (D : xi_leyang_norm_one_unit_explicit_3torsion_data) : ℚ :=
  (D.xi_leyang_norm_one_unit_explicit_3torsion_A -
      3 * D.xi_leyang_norm_one_unit_explicit_3torsion_s *
        D.xi_leyang_norm_one_unit_explicit_3torsion_u) /
    (16 * (2 * D.xi_leyang_norm_one_unit_explicit_3torsion_y + 1) ^ 3)

/-- The hyperelliptic conjugate of `eta`, obtained by sending `u` to `-u`. -/
def xi_leyang_norm_one_unit_explicit_3torsion_iota_eta
    (D : xi_leyang_norm_one_unit_explicit_3torsion_data) : ℚ :=
  (D.xi_leyang_norm_one_unit_explicit_3torsion_A +
      3 * D.xi_leyang_norm_one_unit_explicit_3torsion_s *
        D.xi_leyang_norm_one_unit_explicit_3torsion_u) /
    (16 * (2 * D.xi_leyang_norm_one_unit_explicit_3torsion_y + 1) ^ 3)

/-- Paper-facing statement: the conjugate is the inverse, the norm is one, the divisor is
`3(Qminus - Qplus)`, and the induced divisor class is a nonzero `3`-torsion point. -/
def xi_leyang_norm_one_unit_explicit_3torsion_statement
    (D : xi_leyang_norm_one_unit_explicit_3torsion_data) : Prop :=
  D.xi_leyang_norm_one_unit_explicit_3torsion_iota_eta =
      (D.xi_leyang_norm_one_unit_explicit_3torsion_eta)⁻¹ ∧
    D.xi_leyang_norm_one_unit_explicit_3torsion_eta *
        D.xi_leyang_norm_one_unit_explicit_3torsion_iota_eta = 1 ∧
      D.div D.xi_leyang_norm_one_unit_explicit_3torsion_eta =
        (3 : ℕ) • (D.xi_leyang_norm_one_unit_explicit_3torsion_Qminus -
          D.xi_leyang_norm_one_unit_explicit_3torsion_Qplus) ∧
        (3 : ℕ) • D.classMap
            (D.xi_leyang_norm_one_unit_explicit_3torsion_Qminus -
              D.xi_leyang_norm_one_unit_explicit_3torsion_Qplus) = 0 ∧
          D.classMap (D.xi_leyang_norm_one_unit_explicit_3torsion_Qminus -
            D.xi_leyang_norm_one_unit_explicit_3torsion_Qplus) ≠ 0

end xi_leyang_norm_one_unit_explicit_3torsion_data

open xi_leyang_norm_one_unit_explicit_3torsion_data

/-- Paper label: `thm:xi-leyang-norm-one-unit-explicit-3torsion`. -/
theorem paper_xi_leyang_norm_one_unit_explicit_3torsion
    (D : xi_leyang_norm_one_unit_explicit_3torsion_data) :
    xi_leyang_norm_one_unit_explicit_3torsion_statement D := by
  let A : ℚ := D.xi_leyang_norm_one_unit_explicit_3torsion_A
  let B : ℚ := 16 * (2 * D.xi_leyang_norm_one_unit_explicit_3torsion_y + 1) ^ 3
  have hcardano :
      (A - 3 * D.xi_leyang_norm_one_unit_explicit_3torsion_s *
            D.xi_leyang_norm_one_unit_explicit_3torsion_u) *
          (A + 3 * D.xi_leyang_norm_one_unit_explicit_3torsion_s *
            D.xi_leyang_norm_one_unit_explicit_3torsion_u) =
        256 * (2 * D.xi_leyang_norm_one_unit_explicit_3torsion_y + 1) ^ 6 := by
    simpa [A, xi_leyang_norm_one_unit_explicit_3torsion_A] using
      (paper_xi_leyang_cardano_numerator_divisor_visibility
        (s := D.xi_leyang_norm_one_unit_explicit_3torsion_s)
        (y := D.xi_leyang_norm_one_unit_explicit_3torsion_y)
        (u := D.xi_leyang_norm_one_unit_explicit_3torsion_u)
        D.xi_leyang_norm_one_unit_explicit_3torsion_s_sq
        D.xi_leyang_norm_one_unit_explicit_3torsion_curve_eq).1
  have hBsq :
      B ^ 2 = 256 * (2 * D.xi_leyang_norm_one_unit_explicit_3torsion_y + 1) ^ 6 := by
    simp [B]
    ring
  have hnorm :
      D.xi_leyang_norm_one_unit_explicit_3torsion_eta *
          D.xi_leyang_norm_one_unit_explicit_3torsion_iota_eta = 1 := by
    rw [xi_leyang_norm_one_unit_explicit_3torsion_eta,
      xi_leyang_norm_one_unit_explicit_3torsion_iota_eta]
    change
      ((A - 3 * D.xi_leyang_norm_one_unit_explicit_3torsion_s *
            D.xi_leyang_norm_one_unit_explicit_3torsion_u) / B) *
        ((A + 3 * D.xi_leyang_norm_one_unit_explicit_3torsion_s *
            D.xi_leyang_norm_one_unit_explicit_3torsion_u) / B) = 1
    field_simp [B, D.xi_leyang_norm_one_unit_explicit_3torsion_denom_ne_zero]
    rw [hcardano, hBsq]
  have hiota :
      D.xi_leyang_norm_one_unit_explicit_3torsion_iota_eta =
        (D.xi_leyang_norm_one_unit_explicit_3torsion_eta)⁻¹ := by
    have hnorm_comm :
        D.xi_leyang_norm_one_unit_explicit_3torsion_iota_eta *
            D.xi_leyang_norm_one_unit_explicit_3torsion_eta = 1 := by
      rw [mul_comm]
      exact hnorm
    exact (inv_eq_of_mul_eq_one_left hnorm_comm).symm
  have hdiv_den :
      D.div B =
        (3 : ℕ) •
          D.div (2 * D.xi_leyang_norm_one_unit_explicit_3torsion_y + 1) := by
    change
      D.div (16 * (2 * D.xi_leyang_norm_one_unit_explicit_3torsion_y + 1) ^ 3) =
        (3 : ℕ) •
          D.div (2 * D.xi_leyang_norm_one_unit_explicit_3torsion_y + 1)
    rw [D.xi_leyang_norm_one_unit_explicit_3torsion_div_mul,
      D.xi_leyang_norm_one_unit_explicit_3torsion_div_sixteen,
      D.xi_leyang_norm_one_unit_explicit_3torsion_div_pow]
    simp
  have hdiv :
      D.div D.xi_leyang_norm_one_unit_explicit_3torsion_eta =
        (3 : ℕ) • (D.xi_leyang_norm_one_unit_explicit_3torsion_Qminus -
          D.xi_leyang_norm_one_unit_explicit_3torsion_Qplus) := by
    rw [xi_leyang_norm_one_unit_explicit_3torsion_eta]
    change
      D.div ((A - 3 * D.xi_leyang_norm_one_unit_explicit_3torsion_s *
          D.xi_leyang_norm_one_unit_explicit_3torsion_u) / B) =
        (3 : ℕ) • (D.xi_leyang_norm_one_unit_explicit_3torsion_Qminus -
          D.xi_leyang_norm_one_unit_explicit_3torsion_Qplus)
    rw [D.xi_leyang_norm_one_unit_explicit_3torsion_div_div, hdiv_den]
    change
      D.div (128 * D.xi_leyang_norm_one_unit_explicit_3torsion_y ^ 3 +
            219 * D.xi_leyang_norm_one_unit_explicit_3torsion_y ^ 2 +
              69 * D.xi_leyang_norm_one_unit_explicit_3torsion_y + 16 -
                3 * D.xi_leyang_norm_one_unit_explicit_3torsion_s *
                  D.xi_leyang_norm_one_unit_explicit_3torsion_u) -
          (3 : ℕ) •
            D.div (2 * D.xi_leyang_norm_one_unit_explicit_3torsion_y + 1) =
        (3 : ℕ) • (D.xi_leyang_norm_one_unit_explicit_3torsion_Qminus -
          D.xi_leyang_norm_one_unit_explicit_3torsion_Qplus)
    rw [D.xi_leyang_norm_one_unit_explicit_3torsion_div_A_minus,
      D.xi_leyang_norm_one_unit_explicit_3torsion_div_two_y_plus_one]
    abel
  have htorsion :
      (3 : ℕ) • D.classMap
        (D.xi_leyang_norm_one_unit_explicit_3torsion_Qminus -
          D.xi_leyang_norm_one_unit_explicit_3torsion_Qplus) = 0 := by
    calc
      (3 : ℕ) • D.classMap
          (D.xi_leyang_norm_one_unit_explicit_3torsion_Qminus -
            D.xi_leyang_norm_one_unit_explicit_3torsion_Qplus)
          = D.classMap ((3 : ℕ) •
              (D.xi_leyang_norm_one_unit_explicit_3torsion_Qminus -
                D.xi_leyang_norm_one_unit_explicit_3torsion_Qplus)) := by
        rw [map_nsmul]
      _ = D.classMap (D.div D.xi_leyang_norm_one_unit_explicit_3torsion_eta) := by
        rw [hdiv]
      _ = 0 := by
        simpa [xi_leyang_norm_one_unit_explicit_3torsion_eta,
          xi_leyang_norm_one_unit_explicit_3torsion_A] using
          D.xi_leyang_norm_one_unit_explicit_3torsion_principal_eta
  exact ⟨hiota, hnorm, hdiv, htorsion,
    D.xi_leyang_norm_one_unit_explicit_3torsion_genus_obstruction⟩

end Omega.Zeta
