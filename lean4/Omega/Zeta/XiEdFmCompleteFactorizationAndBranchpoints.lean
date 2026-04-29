import Mathlib.Tactic

namespace Omega.Zeta

/-- The quadratic coefficient \(A(m)=(m-2)(m+2)^2\). -/
def xi_ed_fm_complete_factorization_and_branchpoints_A (m : ℤ) : ℤ :=
  (m - 2) * (m + 2) ^ 2

/-- The linear coefficient \(B(m)=4m^2-17\). -/
def xi_ed_fm_complete_factorization_and_branchpoints_B (m : ℤ) : ℤ :=
  4 * m ^ 2 - 17

/-- The bivariate form \(F(m,y)=A(m)y^2+B(m)y+(4m-7)\). -/
def xi_ed_fm_complete_factorization_and_branchpoints_F (m y : ℤ) : ℤ :=
  xi_ed_fm_complete_factorization_and_branchpoints_A m * y ^ 2 +
    xi_ed_fm_complete_factorization_and_branchpoints_B m * y + (4 * m - 7)

/-- The formal derivative \(\partial F/\partial m\). -/
def xi_ed_fm_complete_factorization_and_branchpoints_Fm (m y : ℤ) : ℤ :=
  (m + 2) * (3 * m - 2) * y ^ 2 + 8 * m * y + 4

/-- The Lee--Yang cubic \(g(y)\). -/
def xi_ed_fm_complete_factorization_and_branchpoints_g (y : ℤ) : ℤ :=
  256 * y ^ 3 + 411 * y ^ 2 + 165 * y + 32

/-- The eliminated cubic \(h(m)\). -/
def xi_ed_fm_complete_factorization_and_branchpoints_h (m : ℤ) : ℤ :=
  16 * m ^ 3 - 87 * m ^ 2 + 186 * m - 128

/-- Numerator after substituting \(y=-2/(m+2)\) in \(F(m,y)\). -/
def xi_ed_fm_complete_factorization_and_branchpoints_firstBranchNumerator (m : ℤ) : ℤ :=
  4 * xi_ed_fm_complete_factorization_and_branchpoints_A m -
    2 * xi_ed_fm_complete_factorization_and_branchpoints_B m * (m + 2) +
      (4 * m - 7) * (m + 2) ^ 2

/-- Numerator after substituting \(y=-2/(3m-2)\) in \(F(m,y)\). -/
def xi_ed_fm_complete_factorization_and_branchpoints_secondBranchNumerator (m : ℤ) : ℤ :=
  4 * xi_ed_fm_complete_factorization_and_branchpoints_A m -
    2 * xi_ed_fm_complete_factorization_and_branchpoints_B m * (3 * m - 2) +
      (4 * m - 7) * (3 * m - 2) ^ 2

/-- Numerator after substituting \(m=2(y-1)/(3y)\) in \(h(m)\). -/
def xi_ed_fm_complete_factorization_and_branchpoints_hToGNumerator (y : ℤ) : ℤ :=
  16 * (2 * (y - 1)) ^ 3 - 87 * (2 * (y - 1)) ^ 2 * (3 * y) +
    186 * (2 * (y - 1)) * (3 * y) ^ 2 - 128 * (3 * y) ^ 3

/-- Paper statement for the formal derivative factorization and branchpoint eliminations. -/
def xi_ed_fm_complete_factorization_and_branchpoints_statement : Prop :=
  (∀ m y : ℤ,
    xi_ed_fm_complete_factorization_and_branchpoints_Fm m y =
      (m * y + 2 * y + 2) * (3 * m * y - 2 * y + 2)) ∧
    (∀ m : ℤ,
      xi_ed_fm_complete_factorization_and_branchpoints_firstBranchNumerator m =
        (m + 2) * (m + 4)) ∧
      (∀ m : ℤ,
        xi_ed_fm_complete_factorization_and_branchpoints_secondBranchNumerator m =
          xi_ed_fm_complete_factorization_and_branchpoints_h m) ∧
        ∀ y : ℤ,
          xi_ed_fm_complete_factorization_and_branchpoints_hToGNumerator y =
            -4 * xi_ed_fm_complete_factorization_and_branchpoints_g y

/-- Paper label: `prop:xi-ed-Fm-complete-factorization-and-branchpoints`. -/
theorem paper_xi_ed_fm_complete_factorization_and_branchpoints :
    xi_ed_fm_complete_factorization_and_branchpoints_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m y
    simp [xi_ed_fm_complete_factorization_and_branchpoints_Fm]
    ring
  · intro m
    simp [xi_ed_fm_complete_factorization_and_branchpoints_firstBranchNumerator,
      xi_ed_fm_complete_factorization_and_branchpoints_A,
      xi_ed_fm_complete_factorization_and_branchpoints_B]
    ring
  · intro m
    simp [xi_ed_fm_complete_factorization_and_branchpoints_secondBranchNumerator,
      xi_ed_fm_complete_factorization_and_branchpoints_A,
      xi_ed_fm_complete_factorization_and_branchpoints_B,
      xi_ed_fm_complete_factorization_and_branchpoints_h]
    ring
  · intro y
    simp [xi_ed_fm_complete_factorization_and_branchpoints_hToGNumerator,
      xi_ed_fm_complete_factorization_and_branchpoints_g]
    ring

end Omega.Zeta
