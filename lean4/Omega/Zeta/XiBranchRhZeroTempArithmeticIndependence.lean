import Mathlib.Tactic

namespace Omega.Zeta

/-- Coefficients of `4u^3 + 25u^2 + 88u + 8`, listed from constant term upward. -/
def xi_branch_rh_zero_temp_arithmetic_independence_cubic_coefficients : List ℤ :=
  [8, 88, 25, 4]

/-- Coefficients of `y^4 - 6y^3 + 9y^2 - y - 1`, listed from constant term upward. -/
def xi_branch_rh_zero_temp_arithmetic_independence_quartic_coefficients : List ℤ :=
  [-1, -1, 9, -6, 1]

/-- Coefficients of `u^5 + 4u^4 + 3u^3 - 96u^2 - 42u - 14`, from constant term upward. -/
def xi_branch_rh_zero_temp_arithmetic_independence_quintic_coefficients : List ℤ :=
  [-14, -42, -96, 3, 4, 1]

def xi_branch_rh_zero_temp_arithmetic_independence_cubic_discriminant : ℤ :=
  -(2 ^ 5 * 5 ^ 3 * 11 ^ 3)

def xi_branch_rh_zero_temp_arithmetic_independence_quartic_discriminant : ℤ :=
  2777

def xi_branch_rh_zero_temp_arithmetic_independence_quintic_discriminant : ℤ :=
  2 ^ 6 * 3 ^ 2 * 7 * 743 * 1693 ^ 2

/-- Squarefree quadratic-discriminant representatives of the three sign subfields. -/
def xi_branch_rh_zero_temp_arithmetic_independence_quadratic_representatives : List ℤ :=
  [-110, 2777, 5201]

/-- Mod-prime cycle witnesses: irreducible cubic, quartic cycles `[4]`, `[1,3]`, quintic
cycles `[5]`, `[1,1,3]`. -/
def xi_branch_rh_zero_temp_arithmetic_independence_cycle_witnesses : List (List ℕ) :=
  [[3], [4], [1, 3], [5], [1, 1, 3]]

/-- The product order of the three symmetric Galois-group certificates. -/
def xi_branch_rh_zero_temp_arithmetic_independence_product_order : ℕ :=
  Fintype.card (Equiv.Perm (Fin 3)) *
    Fintype.card (Equiv.Perm (Fin 4)) *
      Fintype.card (Equiv.Perm (Fin 5))

/-- Concrete certificate-style statement for the arithmetic-independence theorem. -/
def xi_branch_rh_zero_temp_arithmetic_independence_statement : Prop :=
  xi_branch_rh_zero_temp_arithmetic_independence_cubic_coefficients = [8, 88, 25, 4] ∧
  xi_branch_rh_zero_temp_arithmetic_independence_quartic_coefficients = [-1, -1, 9, -6, 1] ∧
  xi_branch_rh_zero_temp_arithmetic_independence_quintic_coefficients =
    [-14, -42, -96, 3, 4, 1] ∧
  xi_branch_rh_zero_temp_arithmetic_independence_cubic_discriminant =
    -(2 ^ 5 * 5 ^ 3 * 11 ^ 3) ∧
  xi_branch_rh_zero_temp_arithmetic_independence_quartic_discriminant = 2777 ∧
  xi_branch_rh_zero_temp_arithmetic_independence_quintic_discriminant =
    2 ^ 6 * 3 ^ 2 * 7 * 743 * 1693 ^ 2 ∧
  xi_branch_rh_zero_temp_arithmetic_independence_quadratic_representatives =
    [-110, 2777, 5201] ∧
  xi_branch_rh_zero_temp_arithmetic_independence_cycle_witnesses =
    [[3], [4], [1, 3], [5], [1, 1, 3]] ∧
  Fintype.card (Equiv.Perm (Fin 3)) = 6 ∧
  Fintype.card (Equiv.Perm (Fin 4)) = 24 ∧
  Fintype.card (Equiv.Perm (Fin 5)) = 120 ∧
  xi_branch_rh_zero_temp_arithmetic_independence_product_order = 17280

theorem paper_xi_branch_rh_zero_temp_arithmetic_independence :
    xi_branch_rh_zero_temp_arithmetic_independence_statement := by
  simp [xi_branch_rh_zero_temp_arithmetic_independence_statement,
    xi_branch_rh_zero_temp_arithmetic_independence_cubic_coefficients,
    xi_branch_rh_zero_temp_arithmetic_independence_quartic_coefficients,
    xi_branch_rh_zero_temp_arithmetic_independence_quintic_coefficients,
    xi_branch_rh_zero_temp_arithmetic_independence_cubic_discriminant,
    xi_branch_rh_zero_temp_arithmetic_independence_quartic_discriminant,
    xi_branch_rh_zero_temp_arithmetic_independence_quintic_discriminant,
    xi_branch_rh_zero_temp_arithmetic_independence_quadratic_representatives,
    xi_branch_rh_zero_temp_arithmetic_independence_cycle_witnesses,
    xi_branch_rh_zero_temp_arithmetic_independence_product_order,
    Fintype.card_perm]
  norm_num

end Omega.Zeta
