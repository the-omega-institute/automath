import Mathlib.Tactic

namespace Omega.Zeta

/-- The quadratic coefficient \(A(m)=(m-2)(m+2)^2\). -/
def xi_ed_bivariate_double_discriminant_identities_A (m : ℤ) : ℤ :=
  (m - 2) * (m + 2) ^ 2

/-- The linear coefficient \(B(m)=4m^2-17\). -/
def xi_ed_bivariate_double_discriminant_identities_B (m : ℤ) : ℤ :=
  4 * m ^ 2 - 17

/-- The bivariate form \(F(m,y)=A(m)y^2+B(m)y+(4m-7)\). -/
def xi_ed_bivariate_double_discriminant_identities_F (m y : ℤ) : ℤ :=
  xi_ed_bivariate_double_discriminant_identities_A m * y ^ 2 +
    xi_ed_bivariate_double_discriminant_identities_B m * y + (4 * m - 7)

/-- The Lee--Yang cubic \(g(y)\). -/
def xi_ed_bivariate_double_discriminant_identities_g (y : ℤ) : ℤ :=
  256 * y ^ 3 + 411 * y ^ 2 + 165 * y + 32

/-- The square-class discriminant representative \(\Delta(y)\). -/
def xi_ed_bivariate_double_discriminant_identities_Delta (y : ℤ) : ℤ :=
  -y * (y - 1) * xi_ed_bivariate_double_discriminant_identities_g y

/-- The discriminant formula for \(F\) as a cubic in \(m\). -/
def xi_ed_bivariate_double_discriminant_identities_cubicDiscriminant (y : ℤ) : ℤ :=
  let a := y ^ 2
  let b := 2 * y ^ 2 + 4 * y
  let c := -4 * y ^ 2 + 4
  let d := -8 * y ^ 2 - 17 * y - 7
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 +
    18 * a * b * c * d

/-- Paper statement for the two discriminant identities of the same bivariate form. -/
def xi_ed_bivariate_double_discriminant_identities_statement : Prop :=
  (∀ m : ℤ,
    xi_ed_bivariate_double_discriminant_identities_B m ^ 2 -
        4 * xi_ed_bivariate_double_discriminant_identities_A m * (4 * m - 7) =
      -4 * m ^ 3 - 16 * m ^ 2 + 16 * m + 65) ∧
    ∀ y : ℤ,
      xi_ed_bivariate_double_discriminant_identities_cubicDiscriminant y =
          -y ^ 3 * (y - 1) * xi_ed_bivariate_double_discriminant_identities_g y ∧
        xi_ed_bivariate_double_discriminant_identities_cubicDiscriminant y =
          y ^ 2 * xi_ed_bivariate_double_discriminant_identities_Delta y

/-- Paper label: `prop:xi-ed-bivariate-double-discriminant-identities`. -/
theorem paper_xi_ed_bivariate_double_discriminant_identities :
    xi_ed_bivariate_double_discriminant_identities_statement := by
  refine ⟨?_, ?_⟩
  · intro m
    simp [xi_ed_bivariate_double_discriminant_identities_A,
      xi_ed_bivariate_double_discriminant_identities_B]
    ring
  · intro y
    constructor
    · simp [xi_ed_bivariate_double_discriminant_identities_cubicDiscriminant,
        xi_ed_bivariate_double_discriminant_identities_g]
      ring
    · simp [xi_ed_bivariate_double_discriminant_identities_cubicDiscriminant,
        xi_ed_bivariate_double_discriminant_identities_Delta,
        xi_ed_bivariate_double_discriminant_identities_g]
      ring

end Omega.Zeta
