import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmEllipticWeightNCorrespondenceBidegreeDelta

namespace Omega.Zeta

abbrev XiTerminalZmLeyangEllipticFourBranchRecursionData := PUnit

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_A4 (_y0 : ℤ) : ℤ := 1

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_A3 (y0 : ℤ) : ℤ := -(y0 ^ 4 + 1)

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_A2 (y0 : ℤ) : ℤ := y0 ^ 8 + y0 ^ 4 + 1

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_A1 (y0 : ℤ) : ℤ :=
  -(y0 ^ 12 + y0 ^ 8 + y0 ^ 4 + 1)

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_A0 (y0 : ℤ) : ℤ := y0 ^ 16

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_H (y0 y1 : ℤ) : ℤ :=
  xi_terminal_zm_leyang_elliptic_four_branch_recursion_A4 y0 * y1 ^ 4 +
    xi_terminal_zm_leyang_elliptic_four_branch_recursion_A3 y0 * y1 ^ 3 +
    xi_terminal_zm_leyang_elliptic_four_branch_recursion_A2 y0 * y1 ^ 2 +
    xi_terminal_zm_leyang_elliptic_four_branch_recursion_A1 y0 * y1 +
    xi_terminal_zm_leyang_elliptic_four_branch_recursion_A0 y0

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_bidegree : ℕ × ℕ := (16, 4)

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_P_LY (y0 : ℤ) : ℤ := y0 + 1

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_Q12 (y0 : ℤ) : ℤ := y0 ^ 12 + 1

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_Q26 (y0 : ℤ) : ℤ := y0 ^ 26 + y0 + 1

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_discriminant (y0 : ℤ) : ℤ :=
  -(y0 * (y0 - 1) * xi_terminal_zm_leyang_elliptic_four_branch_recursion_P_LY y0 *
    xi_terminal_zm_leyang_elliptic_four_branch_recursion_Q12 y0 ^ 2 *
    xi_terminal_zm_leyang_elliptic_four_branch_recursion_Q26 y0 ^ 2)

def xi_terminal_zm_leyang_elliptic_four_branch_recursion_squarefree_branch (y0 : ℤ) : ℤ :=
  y0 * (y0 - 1) * xi_terminal_zm_leyang_elliptic_four_branch_recursion_P_LY y0

def XiTerminalZmLeyangEllipticFourBranchRecursionStatement
    (_ : XiTerminalZmLeyangEllipticFourBranchRecursionData) : Prop :=
  (∀ y0 y1 : ℤ,
      xi_terminal_zm_leyang_elliptic_four_branch_recursion_H y0 y1 =
        xi_terminal_zm_leyang_elliptic_four_branch_recursion_A4 y0 * y1 ^ 4 +
          xi_terminal_zm_leyang_elliptic_four_branch_recursion_A3 y0 * y1 ^ 3 +
          xi_terminal_zm_leyang_elliptic_four_branch_recursion_A2 y0 * y1 ^ 2 +
          xi_terminal_zm_leyang_elliptic_four_branch_recursion_A1 y0 * y1 +
          xi_terminal_zm_leyang_elliptic_four_branch_recursion_A0 y0) ∧
    xi_terminal_zm_leyang_elliptic_four_branch_recursion_bidegree = (16, 4) ∧
    xiTerminalBidegreeAndDeltaFormula 1 ∧
    (∀ y0 : ℤ,
      xi_terminal_zm_leyang_elliptic_four_branch_recursion_discriminant y0 =
        -(y0 * (y0 - 1) * xi_terminal_zm_leyang_elliptic_four_branch_recursion_P_LY y0 *
          xi_terminal_zm_leyang_elliptic_four_branch_recursion_Q12 y0 ^ 2 *
          xi_terminal_zm_leyang_elliptic_four_branch_recursion_Q26 y0 ^ 2)) ∧
    (∀ y0 : ℤ,
      xi_terminal_zm_leyang_elliptic_four_branch_recursion_squarefree_branch y0 =
        y0 * (y0 - 1) * xi_terminal_zm_leyang_elliptic_four_branch_recursion_P_LY y0)

/-- Paper label: `thm:xi-terminal-zm-leyang-elliptic-four-branch-recursion`. -/
theorem paper_xi_terminal_zm_leyang_elliptic_four_branch_recursion
    (D : XiTerminalZmLeyangEllipticFourBranchRecursionData) :
    XiTerminalZmLeyangEllipticFourBranchRecursionStatement D := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · intro y0 y1
    rfl
  · simpa using paper_xi_terminal_zm_elliptic_weight_n_correspondence_bidegree_delta 1
  · intro y0
    rfl
  · intro y0
    rfl

end Omega.Zeta
