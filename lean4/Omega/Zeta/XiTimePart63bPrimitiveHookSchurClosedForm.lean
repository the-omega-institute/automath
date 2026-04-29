import Mathlib.Tactic
import Omega.Zeta.XiTimePart63bCyclicKernelLayerDivisorMobius
import Omega.Zeta.XiTimePart63bQcycleHookSchurProjection

namespace Omega.Zeta

open scoped BigOperators

/-- The hook sign `(-1)^j` used in the single-cycle Schur column. -/
def xi_time_part63b_primitive_hook_schur_closed_form_hook_sign (j : ℕ) : ℚ :=
  if j % 2 = 0 then 1 else -1

/-- The hook-Schur projection
`∑_{j=0}^{r-1} (-1)^j / binom(r-1,j) T_{r,j}` written with the hook encoded by `j`. -/
def xi_time_part63b_primitive_hook_schur_closed_form_hook_projection
    (r : ℕ) (T : ℕ → ℕ → ℚ) : ℚ :=
  (Finset.range r).sum fun j =>
    xi_time_part63b_primitive_hook_schur_closed_form_hook_sign j /
      (Nat.choose (r - 1) j : ℚ) * T r j

/-- Möbius primitive-count divisor sum before substituting the hook-Schur projection. -/
def xi_time_part63b_primitive_hook_schur_closed_form_mobius_sum
    (n : ℕ) (mu S : ℕ → ℚ) : ℚ :=
  (1 / (n : ℚ)) * (Nat.divisors n).sum fun d => mu d * S (n / d)

/-- The primitive-count formula supplied by Möbius inversion. -/
def xi_time_part63b_primitive_hook_schur_closed_form_mobius_formula
    (b mu S : ℕ → ℚ) : Prop :=
  ∀ n, 1 ≤ n →
    b n = xi_time_part63b_primitive_hook_schur_closed_form_mobius_sum n mu S

/-- The hook-Schur projection formula for each cyclic trace layer. -/
def xi_time_part63b_primitive_hook_schur_closed_form_projection_formula
    (S : ℕ → ℚ) (T : ℕ → ℕ → ℚ) : Prop :=
  ∀ r, S r = xi_time_part63b_primitive_hook_schur_closed_form_hook_projection r T

/-- The closed primitive divisor sum after substituting the hook-Schur projection. -/
def xi_time_part63b_primitive_hook_schur_closed_form_formula
    (b mu : ℕ → ℚ) (T : ℕ → ℕ → ℚ) : Prop :=
  ∀ n, 1 ≤ n →
    b n =
      xi_time_part63b_primitive_hook_schur_closed_form_mobius_sum n mu
        (fun r => xi_time_part63b_primitive_hook_schur_closed_form_hook_projection r T)

/-- Paper-facing statement for the primitive hook-Schur closed form. -/
def xi_time_part63b_primitive_hook_schur_closed_form_statement : Prop :=
  ∀ (b mu S : ℕ → ℚ) (T : ℕ → ℕ → ℚ),
    xi_time_part63b_primitive_hook_schur_closed_form_mobius_formula b mu S →
      xi_time_part63b_primitive_hook_schur_closed_form_projection_formula S T →
        xi_time_part63b_primitive_hook_schur_closed_form_formula b mu T

/-- Paper label: `cor:xi-time-part63b-primitive-hook-schur-closed-form`. -/
theorem paper_xi_time_part63b_primitive_hook_schur_closed_form :
    xi_time_part63b_primitive_hook_schur_closed_form_statement := by
  intro b mu S T hmobius hprojection n hn
  rw [hmobius n hn]
  unfold xi_time_part63b_primitive_hook_schur_closed_form_mobius_sum
  congr 1
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [hprojection (n / d)]

end Omega.Zeta
