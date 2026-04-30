import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-leyang-square-descent-discriminant-index`. -/
theorem paper_xi_terminal_zm_leyang_square_descent_discriminant_index :
    (let b : ℤ := -42
     let c : ℤ := 441
     let d : ℤ := -1281424
     b ^ 2 * c ^ 2 - 4 * c ^ 3 - 4 * b ^ 3 * d - 27 * d ^ 2 + 18 * b * c * d =
       -((2 : ℤ) ^ 6 * 3 ^ 5 * 31 ^ 2 * 37 * 283 ^ 2)) ∧
      (((2 : ℕ) ^ 3 * 3 * 31 * 283) ^ 2 =
        (2 : ℕ) ^ 6 * 3 ^ 2 * 31 ^ 2 * 283 ^ 2) := by
  norm_num

end Omega.Zeta
