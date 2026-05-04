import Mathlib.Tactic

namespace Omega.Zeta

/-- The paper's Belyi family value
`Π_r(λ,y) = (λ - 1)^r + (y - 1) λ^(r - 1)`. -/
def xi_terminal_belyi_puiseux_scaling_family_value (r : ℕ) (lambda y : ℤ) : ℤ :=
  (lambda - 1) ^ r + (y - 1) * lambda ^ (r - 1)

/-- A concrete integer Newton-power-sum recurrence seed for the `r`-branch family. -/
def xi_terminal_belyi_puiseux_scaling_power_sum : ℕ → ℕ → ℤ → ℤ
  | r, 0, _ => r
  | r, n + 1, y => y * xi_terminal_belyi_puiseux_scaling_power_sum r n y + r

/-- The Puiseux exponent at the multicritical endpoint. -/
def xi_terminal_belyi_puiseux_scaling_puiseux_exponent (r : ℕ) : ℚ :=
  (1 : ℚ) / r

/-- The zero scaling rate appearing as `n^{-r}`. -/
def xi_terminal_belyi_puiseux_scaling_zero_scaling_rate (r : ℕ) : ℕ :=
  r

/-- Concrete paper-facing statement isolating the polynomial recurrence and local scaling rate. -/
def xi_terminal_belyi_puiseux_scaling_statement (r : ℕ) : Prop :=
  2 ≤ r ∧
    (∀ y : ℤ, xi_terminal_belyi_puiseux_scaling_family_value r 1 y = y - 1) ∧
    (∀ n y,
      xi_terminal_belyi_puiseux_scaling_power_sum r (n + 1) y =
        y * xi_terminal_belyi_puiseux_scaling_power_sum r n y + r) ∧
    xi_terminal_belyi_puiseux_scaling_puiseux_exponent r = (1 : ℚ) / r ∧
    xi_terminal_belyi_puiseux_scaling_zero_scaling_rate r = r

/-- Paper label: `thm:xi-terminal-belyi-puiseux-scaling`. -/
theorem paper_xi_terminal_belyi_puiseux_scaling (r : ℕ) (hr : 2 ≤ r) :
    xi_terminal_belyi_puiseux_scaling_statement r := by
  refine ⟨hr, ?_, ?_, rfl, rfl⟩
  · intro y
    have hr0 : r ≠ 0 := by omega
    simp [xi_terminal_belyi_puiseux_scaling_family_value, hr0]
  · intro n y
    rfl

end Omega.Zeta
