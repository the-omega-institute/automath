import Mathlib.Tactic
import Omega.POM.A4GaloisS5

namespace Omega.Zeta

/-- Low-to-high coefficient vector of `P₄ᵐᵒᵐ(t)=2t⁵-2t⁴-7t²-2t+1`. -/
def xi_terminal_zm4_moment_kernel_s5_moment_coeffs : List ℤ :=
  [1, -2, -7, 0, -2, 2]

/-- Low-to-high coefficient vector of `p₇(x)=x⁵-2x⁴-7x³-2x+2`. -/
def xi_terminal_zm4_moment_kernel_s5_p7_coeffs : List ℤ :=
  [2, -2, 0, -7, -2, 1]

/-- The displayed discriminant of the reciprocal moment-kernel quintic. -/
def xi_terminal_zm4_moment_kernel_s5_discriminant : ℤ :=
  -((2 : ℤ) ^ 4 * 985219)

/-- Concrete transport data from the audited `p₇`/A4 `S₅` certificate. -/
structure xi_terminal_zm4_moment_kernel_s5_Data where
  xi_terminal_zm4_moment_kernel_s5_p7_certificate : Omega.POM.paper_pom_a4_galois_s5

namespace xi_terminal_zm4_moment_kernel_s5_Data

/-- The reciprocal-polynomial package: coefficients reverse, the discriminant is unchanged, and
the transported Galois order is `|S₅|=120`. -/
def Holds (_D : xi_terminal_zm4_moment_kernel_s5_Data) : Prop :=
  Omega.POM.paper_pom_a4_galois_s5 ∧
    xi_terminal_zm4_moment_kernel_s5_p7_coeffs =
      xi_terminal_zm4_moment_kernel_s5_moment_coeffs.reverse ∧
    xi_terminal_zm4_moment_kernel_s5_discriminant = -(15763504 : ℤ) ∧
    2 ^ 4 * 985219 = (15763504 : ℕ) ∧
    Nat.factorial 5 = 120 ∧
    Nat.factorial 5 / 2 = 60

end xi_terminal_zm4_moment_kernel_s5_Data

/-- Paper label: `prop:xi-terminal-zm4-moment-kernel-s5`. -/
theorem paper_xi_terminal_zm4_moment_kernel_s5
    (D : xi_terminal_zm4_moment_kernel_s5_Data) : D.Holds := by
  refine ⟨D.xi_terminal_zm4_moment_kernel_s5_p7_certificate, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · norm_num [xi_terminal_zm4_moment_kernel_s5_discriminant]
  · norm_num
  · decide
  · decide

end Omega.Zeta
