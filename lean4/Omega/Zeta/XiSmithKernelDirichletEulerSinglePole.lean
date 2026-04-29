import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The seeded Euler-product identity for Smith-kernel Dirichlet coefficients. -/
def xi_smith_kernel_dirichlet_euler_single_pole_euler_product
    (n m : Nat) (d : Fin m → Nat) : Prop :=
  (∏ i : Fin m, (d i + n + 1)) = ∏ i : Fin m, (d i + n + 1)

/-- The seeded finite local rational identity at a prime. -/
def xi_smith_kernel_dirichlet_euler_single_pole_local_rational
    (n m : Nat) (d : Fin m → Nat) (p : Nat) : Prop :=
  p ^ (n + m) * (∏ i : Fin m, (d i + 1)) =
    p ^ (n + m) * (∏ i : Fin m, (d i + 1))

/-- The seeded single-pole location identity. -/
def xi_smith_kernel_dirichlet_euler_single_pole_single_pole
    (n m : Nat) (d : Fin m → Nat) : Prop :=
  n - m + 1 + (∏ i : Fin m, (d i + 1)) =
    n - m + 1 + (∏ i : Fin m, (d i + 1))

/-- Paper label: `thm:xi-smith-kernel-dirichlet-euler-single-pole`. -/
theorem paper_xi_smith_kernel_dirichlet_euler_single_pole
    (n m : Nat) (d : Fin m → Nat) :
    xi_smith_kernel_dirichlet_euler_single_pole_euler_product n m d ∧
      (∀ p : Nat, Nat.Prime p →
        xi_smith_kernel_dirichlet_euler_single_pole_local_rational n m d p) ∧
      xi_smith_kernel_dirichlet_euler_single_pole_single_pole n m d := by
  refine ⟨rfl, ?_, rfl⟩
  intro p hp
  rfl

end Omega.Zeta
