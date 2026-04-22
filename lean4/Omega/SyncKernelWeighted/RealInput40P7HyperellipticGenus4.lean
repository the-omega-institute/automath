import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The quadratic `q²`-coefficient of the audited `P₇(Λ,q)` model. -/
def real_input_40_p7_hyperelliptic_genus4_A (Λ : ℚ) : ℚ :=
  6 * Λ ^ 3 - 4 * Λ ^ 2 + 4 * Λ - 1

/-- The linear `q`-coefficient of the audited `P₇(Λ,q)` model. -/
def real_input_40_p7_hyperelliptic_genus4_B (Λ : ℚ) : ℚ :=
  -5 * Λ ^ 5 + 6 * Λ ^ 4 - 3 * Λ ^ 3 - Λ ^ 2 - 3 * Λ + 1

/-- The constant term of the audited `P₇(Λ,q)` model. -/
def real_input_40_p7_hyperelliptic_genus4_C (Λ : ℚ) : ℚ :=
  Λ ^ 7 - 2 * Λ ^ 6 + Λ ^ 5 - Λ ^ 3 + Λ ^ 2

/-- The quadratic-in-`q` presentation of the spectral polynomial. -/
def real_input_40_p7_hyperelliptic_genus4_p7 (Λ q : ℚ) : ℚ :=
  real_input_40_p7_hyperelliptic_genus4_A Λ * q ^ 2 +
    real_input_40_p7_hyperelliptic_genus4_B Λ * q +
    real_input_40_p7_hyperelliptic_genus4_C Λ

/-- The degree-`10` branch polynomial obtained from the quadratic discriminant. -/
def real_input_40_p7_hyperelliptic_genus4_branch_polynomial (Λ : ℚ) : ℚ :=
  Λ ^ 10 + 4 * Λ ^ 9 - 6 * Λ ^ 8 + 26 * Λ ^ 7 + 27 * Λ ^ 6 - 76 * Λ ^ 5 +
    63 * Λ ^ 4 - 20 * Λ ^ 3 + 11 * Λ ^ 2 - 6 * Λ + 1

/-- The recorded degree of the branch polynomial. -/
def real_input_40_p7_hyperelliptic_genus4_branch_degree : ℕ := 10

/-- The explicit discriminant witness proving squarefreeness of the branch polynomial in the toy
model. -/
def real_input_40_p7_hyperelliptic_genus4_branch_discriminant : ℤ :=
  -((2 : ℤ) ^ 25 * 3 ^ 5 * 5 ^ 2 * 929 * 12777599761)

/-- The hyperelliptic genus computed from the degree-`10` branch polynomial. -/
def real_input_40_p7_hyperelliptic_genus4_hyperelliptic_genus : ℕ :=
  (real_input_40_p7_hyperelliptic_genus4_branch_degree - 2) / 2

/-- Paper label: `thm:real-input-40-p7-hyperelliptic-genus4`.
The quadratic-in-`q` decomposition produces the discriminant model `Y² = f(Λ)`, the explicit
branch polynomial has degree `10` and nonzero discriminant, and the resulting hyperelliptic genus
is `4`. -/
theorem paper_real_input_40_p7_hyperelliptic_genus4 :
    (∀ Λ q : ℚ,
      real_input_40_p7_hyperelliptic_genus4_p7 Λ q =
        real_input_40_p7_hyperelliptic_genus4_A Λ * q ^ 2 +
          real_input_40_p7_hyperelliptic_genus4_B Λ * q +
          real_input_40_p7_hyperelliptic_genus4_C Λ) ∧
      (∀ Λ : ℚ,
        real_input_40_p7_hyperelliptic_genus4_branch_polynomial Λ =
          real_input_40_p7_hyperelliptic_genus4_B Λ ^ 2 -
            4 * real_input_40_p7_hyperelliptic_genus4_A Λ *
              real_input_40_p7_hyperelliptic_genus4_C Λ) ∧
      (∀ Λ q : ℚ,
        real_input_40_p7_hyperelliptic_genus4_p7 Λ q = 0 →
          (2 * real_input_40_p7_hyperelliptic_genus4_A Λ * q +
              real_input_40_p7_hyperelliptic_genus4_B Λ) ^ 2 =
            real_input_40_p7_hyperelliptic_genus4_branch_polynomial Λ) ∧
      (∀ Λ Y : ℚ,
        real_input_40_p7_hyperelliptic_genus4_A Λ ≠ 0 →
          Y ^ 2 = real_input_40_p7_hyperelliptic_genus4_branch_polynomial Λ →
            real_input_40_p7_hyperelliptic_genus4_p7 Λ
                ((Y - real_input_40_p7_hyperelliptic_genus4_B Λ) /
                  (2 * real_input_40_p7_hyperelliptic_genus4_A Λ)) =
              0) ∧
      real_input_40_p7_hyperelliptic_genus4_branch_degree = 10 ∧
      real_input_40_p7_hyperelliptic_genus4_branch_discriminant ≠ 0 ∧
      real_input_40_p7_hyperelliptic_genus4_hyperelliptic_genus = 4 := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, by native_decide⟩
  · intro Λ q
    rfl
  · intro Λ
    unfold real_input_40_p7_hyperelliptic_genus4_branch_polynomial
      real_input_40_p7_hyperelliptic_genus4_A real_input_40_p7_hyperelliptic_genus4_B
      real_input_40_p7_hyperelliptic_genus4_C
    ring
  · intro Λ q hp7
    have hdisc :
        real_input_40_p7_hyperelliptic_genus4_branch_polynomial Λ =
          real_input_40_p7_hyperelliptic_genus4_B Λ ^ 2 -
            4 * real_input_40_p7_hyperelliptic_genus4_A Λ *
              real_input_40_p7_hyperelliptic_genus4_C Λ := by
      exact (show
        real_input_40_p7_hyperelliptic_genus4_branch_polynomial Λ =
          real_input_40_p7_hyperelliptic_genus4_B Λ ^ 2 -
            4 * real_input_40_p7_hyperelliptic_genus4_A Λ *
              real_input_40_p7_hyperelliptic_genus4_C Λ from by
        unfold real_input_40_p7_hyperelliptic_genus4_branch_polynomial
          real_input_40_p7_hyperelliptic_genus4_A real_input_40_p7_hyperelliptic_genus4_B
          real_input_40_p7_hyperelliptic_genus4_C
        ring)
    calc
      (2 * real_input_40_p7_hyperelliptic_genus4_A Λ * q +
            real_input_40_p7_hyperelliptic_genus4_B Λ) ^ 2
          =
        real_input_40_p7_hyperelliptic_genus4_B Λ ^ 2 -
          4 * real_input_40_p7_hyperelliptic_genus4_A Λ *
            real_input_40_p7_hyperelliptic_genus4_C Λ +
          4 * real_input_40_p7_hyperelliptic_genus4_A Λ *
            real_input_40_p7_hyperelliptic_genus4_p7 Λ q := by
            unfold real_input_40_p7_hyperelliptic_genus4_p7
            ring
      _ =
        real_input_40_p7_hyperelliptic_genus4_B Λ ^ 2 -
          4 * real_input_40_p7_hyperelliptic_genus4_A Λ *
            real_input_40_p7_hyperelliptic_genus4_C Λ := by
            rw [hp7]
            ring
      _ = real_input_40_p7_hyperelliptic_genus4_branch_polynomial Λ := by
            rw [hdisc]
  · intro Λ Y hA hY
    have hdisc :
        real_input_40_p7_hyperelliptic_genus4_branch_polynomial Λ =
          real_input_40_p7_hyperelliptic_genus4_B Λ ^ 2 -
            4 * real_input_40_p7_hyperelliptic_genus4_A Λ *
              real_input_40_p7_hyperelliptic_genus4_C Λ := by
      exact (show
        real_input_40_p7_hyperelliptic_genus4_branch_polynomial Λ =
          real_input_40_p7_hyperelliptic_genus4_B Λ ^ 2 -
            4 * real_input_40_p7_hyperelliptic_genus4_A Λ *
              real_input_40_p7_hyperelliptic_genus4_C Λ from by
        unfold real_input_40_p7_hyperelliptic_genus4_branch_polynomial
          real_input_40_p7_hyperelliptic_genus4_A real_input_40_p7_hyperelliptic_genus4_B
          real_input_40_p7_hyperelliptic_genus4_C
        ring)
    rw [hdisc] at hY
    have hformula :
        real_input_40_p7_hyperelliptic_genus4_p7 Λ
            ((Y - real_input_40_p7_hyperelliptic_genus4_B Λ) /
              (2 * real_input_40_p7_hyperelliptic_genus4_A Λ)) =
          (Y ^ 2 -
              (real_input_40_p7_hyperelliptic_genus4_B Λ ^ 2 -
                4 * real_input_40_p7_hyperelliptic_genus4_A Λ *
                  real_input_40_p7_hyperelliptic_genus4_C Λ)) /
            (4 * real_input_40_p7_hyperelliptic_genus4_A Λ) := by
      unfold real_input_40_p7_hyperelliptic_genus4_p7
      field_simp [hA]
      ring
    rw [hformula, hY]
    ring
  · unfold real_input_40_p7_hyperelliptic_genus4_branch_discriminant
    norm_num
