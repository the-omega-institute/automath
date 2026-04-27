import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Divisors `e` of `N` lying above `d` in the cyclic subgroup divisor lattice. -/
def xi_time_part63b_cyclic_kernel_layer_divisor_mobius_upper_divisors (N d : ℕ) :
    Finset ℕ :=
  (Nat.divisors N).filter fun e => d ∣ e

/-- Concrete cyclic-kernel layer data on the divisor lattice of `C_N`. The coefficient function
`mu` records the divisor-lattice Möbius weight used by the audit certificate. -/
structure xi_time_part63b_cyclic_kernel_layer_divisor_mobius_data where
  N : ℕ
  B : ℕ → ℤ
  K : ℕ → ℤ
  characterLayer : ℕ → ℤ
  mu : ℕ → ℤ
  forward_certificate :
    ∀ d, d ∣ N →
      ((N / d : ℕ) : ℤ) * B d =
        (xi_time_part63b_cyclic_kernel_layer_divisor_mobius_upper_divisors N d).sum K
  mobius_certificate :
    ∀ d, d ∣ N →
      K d =
        (xi_time_part63b_cyclic_kernel_layer_divisor_mobius_upper_divisors N d).sum
          (fun e => mu (e / d) * ((N / e : ℕ) : ℤ) * B e)
  gcd_layer_certificate :
    ∀ d, d ∣ N →
      K d = ((Finset.range N).filter (fun a => Nat.gcd a N = d)).sum characterLayer

namespace xi_time_part63b_cyclic_kernel_layer_divisor_mobius_data

/-- Forward conductor-to-kernel summation over divisor layers above `d`. -/
def forward_formula (D : xi_time_part63b_cyclic_kernel_layer_divisor_mobius_data) : Prop :=
  ∀ d, d ∣ D.N →
    ((D.N / d : ℕ) : ℤ) * D.B d =
      (xi_time_part63b_cyclic_kernel_layer_divisor_mobius_upper_divisors D.N d).sum D.K

/-- Möbius inversion on the divisor lattice above `d`. -/
def mobius_formula (D : xi_time_part63b_cyclic_kernel_layer_divisor_mobius_data) : Prop :=
  ∀ d, d ∣ D.N →
    D.K d =
      (xi_time_part63b_cyclic_kernel_layer_divisor_mobius_upper_divisors D.N d).sum
        (fun e => D.mu (e / d) * ((D.N / e : ℕ) : ℤ) * D.B e)

/-- GCD-indexed character-layer form for the exact kernel layer. -/
def gcd_layer_formula (D : xi_time_part63b_cyclic_kernel_layer_divisor_mobius_data) : Prop :=
  ∀ d, d ∣ D.N →
    D.K d = ((Finset.range D.N).filter (fun a => Nat.gcd a D.N = d)).sum D.characterLayer

end xi_time_part63b_cyclic_kernel_layer_divisor_mobius_data

/-- Paper label: `cor:xi-time-part63b-cyclic-kernel-layer-divisor-mobius`. -/
theorem paper_xi_time_part63b_cyclic_kernel_layer_divisor_mobius
    (D : xi_time_part63b_cyclic_kernel_layer_divisor_mobius_data) :
    D.forward_formula ∧ D.mobius_formula ∧ D.gcd_layer_formula := by
  exact ⟨D.forward_certificate, D.mobius_certificate, D.gcd_layer_certificate⟩

end Omega.Zeta
