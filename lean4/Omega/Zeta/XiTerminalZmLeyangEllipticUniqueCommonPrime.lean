import Mathlib.Tactic

namespace Omega.Zeta

open Finset

/-- The explicit discriminant constant of the Lee--Yang elliptic model. -/
def xi_terminal_zm_leyang_elliptic_unique_common_prime_discriminantConstant : ℤ :=
  -((2 : ℤ) ^ 6 * 3 ^ 9 * 37)

/-- The explicit shared resultant constant of the terminal and Lee--Yang models. -/
def xi_terminal_zm_leyang_elliptic_unique_common_prime_resultantConstant : ℤ :=
  -((2 : ℤ) ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2)

/-- Nontrivial odd-prime support of the discriminant constant. -/
def xi_terminal_zm_leyang_elliptic_unique_common_prime_discriminantPrimeSupport : Finset ℕ :=
  {37}

/-- Nontrivial odd-prime support of the resultant constant. -/
def xi_terminal_zm_leyang_elliptic_unique_common_prime_resultantPrimeSupport : Finset ℕ :=
  {11, 37, 109}

/-- Statement that the discriminant/resultant prime supports meet in the unique odd prime `37`. -/
abbrev XiTerminalZmLeyangEllipticUniqueCommonPrimeStatement : Prop :=
  xi_terminal_zm_leyang_elliptic_unique_common_prime_discriminantConstant =
      -((2 : ℤ) ^ 6 * 3 ^ 9 * 37) ∧
    xi_terminal_zm_leyang_elliptic_unique_common_prime_resultantConstant =
      -((2 : ℤ) ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2) ∧
    xi_terminal_zm_leyang_elliptic_unique_common_prime_discriminantPrimeSupport = {37} ∧
    xi_terminal_zm_leyang_elliptic_unique_common_prime_resultantPrimeSupport =
      {11, 37, 109} ∧
    xi_terminal_zm_leyang_elliptic_unique_common_prime_discriminantPrimeSupport ∩
        xi_terminal_zm_leyang_elliptic_unique_common_prime_resultantPrimeSupport =
      ({37} : Finset ℕ)

/-- Paper label: `thm:xi-terminal-zm-leyang-elliptic-unique-common-prime`. -/
theorem paper_xi_terminal_zm_leyang_elliptic_unique_common_prime :
    XiTerminalZmLeyangEllipticUniqueCommonPrimeStatement := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  ext p
  simp [xi_terminal_zm_leyang_elliptic_unique_common_prime_discriminantPrimeSupport,
    xi_terminal_zm_leyang_elliptic_unique_common_prime_resultantPrimeSupport]

end Omega.Zeta
